#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fil Obligataire : agrégateur de news financières façon terminal.

    python terminal.py                  lance le terminal sur http://127.0.0.1:8787
    python terminal.py --interval 300   récupère les flux toutes les 300 s (défaut : 180)
    python terminal.py --port 9000      change le port local
    python terminal.py --check          teste chaque source une fois, affiche le bilan et quitte
    python terminal.py --lan            rend aussi le terminal accessible aux appareils du même Wi-Fi (iPhone…)
    python terminal.py --build site     génère une version statique (site/index.html + site/news.json)

Aucune dépendance : bibliothèque standard de Python 3.8 ou plus récent.
"""

from __future__ import annotations

import argparse
import functools
import gzip
import hashlib
import html
import json
import re
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
import zlib
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from html.entities import name2codepoint
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

APP_NAME = "Fil Obligataire"
ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCES = ROOT / "sources.json"
WEB_DIR = ROOT / "web" if (ROOT / "web" / "index.html").exists() else ROOT
INDEX_FILE = WEB_DIR / "index.html"
WEB_FILES = ("index.html", "manifest.webmanifest", "icon-180.png", "icon-512.png")
CACHE_FILE = ROOT / ".fil_cache.json"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/128.0 Safari/537.36 FilObligataire/1.0"
)
TIMEOUT = 15              # secondes accordées à chaque flux
MAX_BYTES = 6_000_000     # taille maximale d'un flux
MAX_PER_SOURCE = 60       # titres gardés par source
KEEP_MIN_PER_SOURCE = 3   # titres toujours gardés, même anciens
MAX_AGE_DAYS = 14         # au-delà, un titre sort du fil
SUMMARY_CHARS = 700       # longueur maximale des résumés
WORKERS = 10              # flux récupérés en parallèle
MIN_MANUAL_GAP = 20       # secondes minimum entre deux actualisations manuelles

CATEGORIES = {"banques-centrales", "institutions", "regulateurs", "presse-fr", "presse-intl"}
CONTENT_TYPES = {
    ".html": "text/html; charset=utf-8",
    ".webmanifest": "application/manifest+json",
    ".png": "image/png",
    ".json": "application/json; charset=utf-8",
}


# --------------------------------------------------------------------------- utilitaires

def now_ms() -> int:
    return int(time.time() * 1000)


def log(msg: str) -> None:
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")


def clean_text(value: str | None) -> str:
    """Retire le HTML et les entités, normalise les espaces."""
    if not value:
        return ""
    s = value
    if "&lt;" in s or "&#60;" in s or "&#x3c;" in s.lower():
        s = html.unescape(s)
    s = TAG_RE.sub(" ", s)
    s = html.unescape(s).replace(" ", " ")
    return WS_RE.sub(" ", s).strip()


def truncate(s: str, n: int) -> str:
    if len(s) <= n:
        return s
    cut = s[:n].rsplit(" ", 1)[0]
    return cut.rstrip(",;:.-– ") + "…"


def norm_link(url: str) -> str:
    """Forme canonique d'un lien pour repérer les doublons."""
    if not url:
        return ""
    try:
        parts = urlsplit(url.strip())
    except ValueError:
        return url.strip()
    query = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
             if not k.lower().startswith(("utm_", "ftag", "ftcamp"))]
    path = parts.path.rstrip("/") or "/"
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(), path, urlencode(query), ""))


@functools.lru_cache(maxsize=1)
def ssl_context() -> ssl.SSLContext:
    """Contexte HTTPS. Sur Mac, ajoute les certificats racines du trousseau système :
    le Python de python.org n'en a aucun tant que « Install Certificates » n'a pas été lancé,
    et le trousseau contient aussi le certificat d'un éventuel proxy d'entreprise."""
    ctx = ssl.create_default_context()
    if sys.platform == "darwin":
        try:
            pem = subprocess.run(
                ["/usr/bin/security", "find-certificate", "-a", "-p",
                 "/System/Library/Keychains/SystemRootCertificates.keychain",
                 "/Library/Keychains/System.keychain"],
                capture_output=True, text=True, timeout=15, check=False,
            ).stdout
        except (OSError, subprocess.SubprocessError):
            pem = ""
        for block in re.findall(r"-----BEGIN CERTIFICATE-----.+?-----END CERTIFICATE-----", pem, re.S):
            try:
                ctx.load_verify_locations(cadata=block)
            except (ssl.SSLError, ValueError):
                continue
    return ctx


# --------------------------------------------------------------------------- dates

FRAC_RE = re.compile(r"\.(\d+)")


def parse_date(value: str | None) -> int | None:
    """Accepte RFC 822 (RSS), ISO 8601 (Atom) et « AAAA-MM-JJ HH:MM:SS »."""
    if not value:
        return None
    s = value.strip()
    if not s:
        return None
    dt = None
    if not re.match(r"^\d{4}-\d{2}-\d{2}", s):
        try:
            dt = parsedate_to_datetime(s)
        except (TypeError, ValueError, IndexError):
            dt = None
    if dt is None:
        iso = s
        if re.match(r"^\d{4}-\d{2}-\d{2} \d", iso):
            iso = iso.replace(" ", "T", 1)
        iso = re.sub(r"[Zz]$", "+00:00", iso)
        iso = re.sub(r"\s*(GMT|UTC)$", "+00:00", iso)
        iso = FRAC_RE.sub(lambda m: "." + m.group(1)[:6].ljust(6, "0"), iso, count=1)
        iso = re.sub(r"([+-]\d{2})(\d{2})$", r"\1:\2", iso)
        try:
            dt = datetime.fromisoformat(iso)
        except ValueError:
            return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return int(dt.timestamp() * 1000)


# --------------------------------------------------------------------------- lecture des flux

XML_ENTITIES = {b"amp", b"lt", b"gt", b"quot", b"apos"}
ENTITY_RE = re.compile(rb"&([A-Za-z][A-Za-z0-9]{1,31});")
BARE_AMP_RE = re.compile(rb"&(?!#[0-9]{1,7};|#[xX][0-9A-Fa-f]{1,6};|[A-Za-z][A-Za-z0-9]{1,31};)")
CTRL_RE = re.compile(rb"[\x00-\x08\x0b\x0c\x0e-\x1f]")


def _entity(m: re.Match) -> bytes:
    name = m.group(1)
    if name in XML_ENTITIES:
        return m.group(0)
    cp = name2codepoint.get(name.decode("ascii", "ignore"))
    if cp is None:
        return b"&amp;" + name + b";"
    return b"&#%d;" % cp


def sanitize_xml(raw: bytes) -> bytes:
    """Répare les erreurs courantes des flux : & isolés, entités HTML, caractères de contrôle."""
    data = CTRL_RE.sub(b"", raw)
    data = BARE_AMP_RE.sub(b"&amp;", data)
    return ENTITY_RE.sub(_entity, data)


def local(tag) -> str:
    if not isinstance(tag, str):
        return ""
    return tag.rsplit("}", 1)[-1].lower()


def text_of(el) -> str:
    return "".join(el.itertext()) if el is not None else ""


DATE_FIELDS = ("pubdate", "published", "issued", "date", "updated", "modified", "created")
SUMMARY_FIELDS = ("description", "summary", "encoded", "content", "abstract")


def parse_feed(raw: bytes) -> list[dict]:
    data = raw[3:] if raw.startswith(b"\xef\xbb\xbf") else raw
    data = data.lstrip()
    try:
        root = ET.fromstring(data)
    except ET.ParseError:
        root = ET.fromstring(sanitize_xml(data))

    out = []
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        fields: dict = {}
        links: list[tuple[str, str]] = []
        for child in el:
            name = local(child.tag)
            if name == "link":
                href = child.get("href")
                if href:
                    links.append(((child.get("rel") or "alternate").lower(), href.strip()))
                elif child.text and child.text.strip():
                    links.append(("alternate", child.text.strip()))
            elif name not in fields:
                fields[name] = child

        title = clean_text(text_of(fields.get("title")))

        link = clean_text(text_of(fields.get("origlink")))
        if not link:
            for rel, href in links:
                if rel == "alternate":
                    link = href
                    break
        if not link and links:
            link = links[0][1]
        if not link:
            guid = clean_text(text_of(fields.get("guid")))
            if guid.startswith(("http://", "https://")):
                link = guid
        if not link:
            about = el.get("{http://www.w3.org/1999/02/22-rdf-syntax-ns#}about", "")
            if about.startswith(("http://", "https://")):
                link = about

        ts = None
        for f in DATE_FIELDS:
            if f in fields:
                ts = parse_date(text_of(fields[f]))
                if ts:
                    break

        summary = ""
        for f in SUMMARY_FIELDS:
            if f in fields:
                summary = clean_text(text_of(fields[f]))
                if summary:
                    break
        if summary == title:
            summary = ""

        if title and link:
            out.append({"title": title, "link": link, "ts": ts, "summary": truncate(summary, SUMMARY_CHARS)})
    return out


def decompress(raw: bytes, encoding: str | None) -> bytes:
    enc = (encoding or "").lower()
    if "gzip" in enc or raw[:2] == b"\x1f\x8b":
        return gzip.decompress(raw)
    if "deflate" in enc:
        try:
            return zlib.decompress(raw)
        except zlib.error:
            return zlib.decompress(raw, -zlib.MAX_WBITS)
    return raw


def describe_url_error(err: urllib.error.URLError) -> str:
    reason = err.reason
    if isinstance(reason, ssl.SSLCertVerificationError):
        return "certificat SSL refusé (proxy d'entreprise ?)"
    if isinstance(reason, (socket.timeout, TimeoutError)):
        return "délai dépassé"
    if isinstance(reason, socket.gaierror):
        return "site introuvable (DNS ou pas de connexion)"
    return str(reason)


# --------------------------------------------------------------------------- agrégation

class SourceState:
    __slots__ = ("etag", "modified", "items", "status", "error", "fetched_at", "ok_at")

    def __init__(self) -> None:
        self.etag: str | None = None
        self.modified: str | None = None
        self.items: list[dict] = []
        self.status = "pending"
        self.error = ""
        self.fetched_at: int | None = None
        self.ok_at: int | None = None


class Aggregator:
    def __init__(self, sources: list[dict], mode: str, interval: int) -> None:
        self.sources = sources
        self.mode = mode
        self.interval = interval
        self.states = {s["code"]: SourceState() for s in sources}
        self.first_seen: dict[str, int] = {}
        self.lock = threading.Lock()
        self.refresh_lock = threading.Lock()
        self.refreshing = False
        self.last_refresh = 0
        self.next_refresh = 0
        self.snapshot: dict = {}
        self.snapshot_bytes = b""
        self.rebuild()

    # -- reprise d'un instantané précédent (cache local ou version en ligne)
    def seed(self, previous: dict | None) -> None:
        if not previous:
            return
        by_src: dict[str, list] = {}
        for it in previous.get("items", []):
            by_src.setdefault(it.get("s"), []).append(it)
            if it.get("id") and it.get("fs"):
                self.first_seen[it["id"]] = it["fs"]
        prev_sources = {p.get("code"): p for p in previous.get("sources", [])}
        for src in self.sources:
            st = self.states[src["code"]]
            st.items = [
                {"title": it.get("t", ""), "link": it.get("u", ""), "ts": it.get("ts"), "summary": it.get("d", "")}
                for it in by_src.get(src["code"], [])
            ]
            prev = prev_sources.get(src["code"])
            if prev:
                st.fetched_at = prev.get("fetched_at")
                st.ok_at = prev.get("ok_at")
        self.rebuild()

    def fetch(self, src: dict) -> None:
        st = self.states[src["code"]]
        headers = {
            "User-Agent": USER_AGENT,
            "Accept": "application/rss+xml, application/atom+xml, application/xml;q=0.9, text/xml;q=0.8, */*;q=0.5",
            "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.8",
            "Accept-Encoding": "gzip, deflate",
        }
        if st.etag:
            headers["If-None-Match"] = st.etag
        if st.modified:
            headers["If-Modified-Since"] = st.modified
        st.fetched_at = now_ms()
        try:
            req = urllib.request.Request(src["url"], headers=headers)
            with urllib.request.urlopen(req, timeout=TIMEOUT, context=ssl_context()) as resp:
                raw = resp.read(MAX_BYTES + 1)
                if len(raw) > MAX_BYTES:
                    raise ValueError("flux trop volumineux")
                raw = decompress(raw, resp.headers.get("Content-Encoding"))
                head = raw[:512].lstrip().lower()
                if head.startswith((b"<!doctype html", b"<html")):
                    raise ValueError("page web reçue au lieu d'un flux (protection anti-robot ou adresse changée)")
                items = parse_feed(raw)
                if not items:
                    raise ValueError("aucun titre : la page reçue n'est pas un flux RSS/Atom")
                st.items = self.postprocess(src, items)
                st.etag = resp.headers.get("ETag")
                st.modified = resp.headers.get("Last-Modified")
            st.status, st.error, st.ok_at = "ok", "", st.fetched_at
        except urllib.error.HTTPError as e:
            if e.code == 304:
                st.status, st.error, st.ok_at = "ok", "", st.fetched_at
            else:
                st.status, st.error = "error", f"HTTP {e.code} {e.reason}".strip()
        except urllib.error.URLError as e:
            st.status, st.error = "error", describe_url_error(e)
        except ET.ParseError:
            st.status, st.error = "error", "contenu illisible (XML invalide)"
        except (socket.timeout, TimeoutError):
            st.status, st.error = "error", "délai dépassé"
        except Exception as e:  # une source cassée ne doit jamais bloquer les autres
            st.status, st.error = "error", (str(e) or e.__class__.__name__)[:200]

    def postprocess(self, src: dict, items: list[dict]) -> list[dict]:
        limit = now_ms() + 6 * 3600 * 1000  # une date trop dans le futur est ignorée
        out = []
        for it in items[: MAX_PER_SOURCE * 2]:
            title = it["title"]
            for suffix in src.get("retirer_suffixe", []):
                if title.endswith(suffix):
                    title = title[: -len(suffix)].rstrip(" -–|")
            link = it["link"]
            if not link.startswith(("http://", "https://")):
                link = urljoin(src["url"], link)
            ts = it["ts"] if it["ts"] and it["ts"] < limit else None
            out.append({"title": title, "link": link, "ts": ts, "summary": it["summary"]})
        return out

    def rebuild(self) -> None:
        now = now_ms()
        cutoff = now - MAX_AGE_DAYS * 86_400_000
        items: list[dict] = []
        seen_links: set[str] = set()
        seen_titles: set[str] = set()
        live_ids: set[str] = set()
        rows = []
        for src in self.sources:
            st = self.states[src["code"]]
            ranked = sorted(st.items, key=lambda it: it.get("ts") or 0, reverse=True)[:MAX_PER_SOURCE]
            kept, latest = 0, None
            for rank, it in enumerate(ranked):
                key = norm_link(it["link"]) or f"{src['code']}:{it['title'].lower()}"
                iid = hashlib.sha1(key.encode("utf-8")).hexdigest()[:12]
                live_ids.add(iid)
                fs = self.first_seen.setdefault(iid, now)
                ts = it.get("ts") or fs
                if ts < cutoff and rank >= KEEP_MIN_PER_SOURCE:
                    continue
                title_key = re.sub(r"\W+", "", it["title"].lower())
                if key in seen_links or (title_key and title_key in seen_titles):
                    continue
                seen_links.add(key)
                seen_titles.add(title_key)
                items.append({"id": iid, "s": src["code"], "t": it["title"], "u": it["link"],
                              "ts": ts, "fs": fs, "d": it.get("summary", "")})
                kept += 1
                latest = ts if latest is None else max(latest, ts)
            rows.append({
                "code": src["code"], "nom": src["nom"], "cat": src["categorie"], "lang": src["langue"],
                "site": src.get("site", ""), "url": src["url"], "status": st.status, "error": st.error,
                "count": kept, "latest": latest, "fetched_at": st.fetched_at, "ok_at": st.ok_at,
            })
        self.first_seen = {k: v for k, v in self.first_seen.items() if k in live_ids}
        items.sort(key=lambda x: (x["ts"], x["fs"]), reverse=True)
        snap = {
            "app": APP_NAME, "version": 1, "mode": self.mode, "generated_at": now,
            "interval": self.interval, "next_refresh": self.next_refresh, "refreshing": self.refreshing,
            "sources": rows, "items": items,
        }
        data = json.dumps(snap, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        with self.lock:
            self.snapshot, self.snapshot_bytes = snap, data

    def refresh(self) -> bool:
        if not self.refresh_lock.acquire(blocking=False):
            return False
        try:
            self.refreshing = True
            self.rebuild()
            with ThreadPoolExecutor(max_workers=WORKERS) as pool:
                list(pool.map(self.fetch, self.sources))
            self.last_refresh = now_ms()
            self.next_refresh = self.last_refresh + self.interval * 1000
            self.refreshing = False
            self.rebuild()
            ok = sum(1 for s in self.states.values() if s.status == "ok")
            log(f"{ok}/{len(self.sources)} sources OK · {len(self.snapshot['items'])} titres dans le fil")
            return True
        finally:
            self.refreshing = False
            self.refresh_lock.release()

    def request_refresh(self, wake: threading.Event) -> bool:
        if self.refreshing or now_ms() - self.last_refresh < MIN_MANUAL_GAP * 1000:
            return False
        wake.set()
        return True

    def save_cache(self) -> None:
        try:
            tmp = CACHE_FILE.with_suffix(".tmp")
            tmp.write_bytes(self.snapshot_bytes)
            tmp.replace(CACHE_FILE)
        except OSError:
            pass


# --------------------------------------------------------------------------- configuration

def load_sources(path: Path) -> list[dict]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        sys.exit(f"Fichier introuvable : {path}")
    except json.JSONDecodeError as e:
        sys.exit(f"{path.name} est invalide (ligne {e.lineno}, colonne {e.colno}) : {e.msg}")
    entries = raw.get("sources", raw) if isinstance(raw, dict) else raw
    sources, codes = [], set()
    for i, src in enumerate(entries, 1):
        if not isinstance(src, dict) or src.get("actif", True) is False:
            continue
        missing = [k for k in ("code", "nom", "url") if not src.get(k)]
        if missing:
            sys.exit(f"{path.name}, source n°{i} : champ(s) manquant(s) {', '.join(missing)}")
        code = str(src["code"]).upper()
        if code in codes:
            sys.exit(f"{path.name} : le code {code} est utilisé deux fois")
        codes.add(code)
        cat = src.get("categorie", "presse-intl")
        if cat not in CATEGORIES:
            sys.exit(f"{path.name}, source {code} : catégorie « {cat} » inconnue ({', '.join(sorted(CATEGORIES))})")
        suffix = src.get("retirer_suffixe", [])
        sources.append({
            "code": code, "nom": src["nom"], "url": src["url"], "categorie": cat,
            "langue": src.get("langue", "en"), "site": src.get("site", ""),
            "retirer_suffixe": [suffix] if isinstance(suffix, str) else list(suffix),
        })
    if not sources:
        sys.exit(f"{path.name} ne contient aucune source active")
    return sources


def read_json_file(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def read_json_url(url: str) -> dict | None:
    try:
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=TIMEOUT, context=ssl_context()) as resp:
            return json.loads(decompress(resp.read(), resp.headers.get("Content-Encoding")))
    except Exception:
        return None


# --------------------------------------------------------------------------- modes

def run_check(agg: Aggregator) -> int:
    print(f"{APP_NAME} : test de {len(agg.sources)} sources…\n")
    agg.refresh()
    print()
    for row in agg.snapshot["sources"]:
        if row["status"] == "ok":
            latest = datetime.fromtimestamp(row["latest"] / 1000).strftime("%d/%m %H:%M") if row["latest"] else "—"
            print(f"  OK   {row['code']:<6} {row['count']:>3} titres  dernier : {latest:<11}  {row['nom']}")
        else:
            print(f"  ERR  {row['code']:<6} {row['error'][:48]:<48}  {row['nom']}")
    bad = sum(1 for r in agg.snapshot["sources"] if r["status"] != "ok")
    print(f"\n{len(agg.sources) - bad} sources OK, {bad} en erreur.")
    return 0


def run_build(agg: Aggregator, out_dir: Path, previous_url: str | None) -> int:
    previous = read_json_file(out_dir / "news.json")
    if previous is None and previous_url:
        previous = read_json_url(previous_url)
        if previous:
            log("Instantané précédent récupéré en ligne")
    agg.seed(previous)
    agg.refresh()
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "news.json").write_bytes(agg.snapshot_bytes)
    for name in WEB_FILES:
        if (WEB_DIR / name).is_file():
            shutil.copyfile(WEB_DIR / name, out_dir / name)
    (out_dir / ".nojekyll").write_text("", encoding="utf-8")
    log(f"Version statique écrite dans {out_dir}")
    return 0


def make_handler(agg: Aggregator, wake: threading.Event):
    class Handler(BaseHTTPRequestHandler):
        server_version = "FilObligataire/1.0"

        def _send(self, code: int, body: bytes, ctype: str) -> None:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)

        def _refresh(self) -> None:
            accepted = agg.request_refresh(wake)
            body = json.dumps({"accepted": accepted}).encode("utf-8")
            self._send(202 if accepted else 429, body, "application/json")

        def do_GET(self) -> None:
            path = urlsplit(self.path).path
            if path == "/":
                path = "/index.html"
            if path == "/news.json":
                with agg.lock:
                    body = agg.snapshot_bytes
                return self._send(200, body, "application/json; charset=utf-8")
            if path == "/refresh":
                return self._refresh()
            if path == "/favicon.ico":
                return self._send(204, b"", "image/x-icon")
            name = path.lstrip("/")
            ctype = CONTENT_TYPES.get(Path(name).suffix.lower())
            if ctype and name in WEB_FILES:
                try:
                    return self._send(200, (WEB_DIR / name).read_bytes(), ctype)
                except OSError:
                    if name == "index.html":
                        return self._send(500, "index.html introuvable à côté de terminal.py".encode("utf-8"),
                                          "text/plain; charset=utf-8")
            self._send(404, b"Not found", "text/plain")

        do_HEAD = do_GET

        def do_POST(self) -> None:
            if urlsplit(self.path).path == "/refresh":
                return self._refresh()
            self._send(404, b"Not found", "text/plain")

        def log_message(self, fmt, *args) -> None:  # console silencieuse
            pass

    return Handler


def lan_urls(port: int) -> list[str]:
    """Adresses à taper sur un iPhone connecté au même Wi-Fi."""
    urls = []
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("192.0.2.1", 80))  # aucune donnée n'est envoyée
            ip = s.getsockname()[0]
        if not ip.startswith("127."):
            urls.append(f"http://{ip}:{port}/")
    except OSError:
        pass
    if sys.platform == "darwin":
        try:
            name = subprocess.run(["scutil", "--get", "LocalHostName"], capture_output=True,
                                  text=True, timeout=5, check=False).stdout.strip()
            if name:
                urls.append(f"http://{name}.local:{port}/")
        except (OSError, subprocess.SubprocessError):
            pass
    return urls


def run_server(agg: Aggregator, port: int, open_browser: bool, lan: bool = False) -> int:
    cached = read_json_file(CACHE_FILE)
    if cached:
        agg.seed(cached)
        log("Derniers titres repris du cache, actualisation en cours…")

    wake = threading.Event()
    handler = make_handler(agg, wake)
    server = None
    for p in range(port, port + 10):
        try:
            server = ThreadingHTTPServer(("0.0.0.0" if lan else "127.0.0.1", p), handler)
            port = p
            break
        except OSError:
            continue
    if server is None:
        sys.exit(f"Aucun port libre entre {port} et {port + 9}. Essaie --port 9100.")
    server.daemon_threads = True

    def loop() -> None:
        while True:
            agg.refresh()
            agg.save_cache()
            wake.wait(agg.interval)
            wake.clear()

    threading.Thread(target=loop, daemon=True).start()
    url = f"http://127.0.0.1:{port}/"
    print(f"\n  {APP_NAME} est lancé : {url}")
    if lan:
        others = lan_urls(port)
        if others:
            print("  Sur ton iPhone (même Wi-Fi) : " + "  ou  ".join(others))
        else:
            print("  Mode Wi-Fi actif, mais aucune adresse réseau détectée (es-tu connecté au Wi-Fi ?)")
    print(f"  Flux récupérés toutes les {agg.interval} s. Ctrl+C pour arrêter.\n", flush=True)
    if open_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        print("\nArrêt.")
    finally:
        agg.save_cache()
        server.server_close()
    return 0


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            try:
                stream.reconfigure(errors="replace")
            except (ValueError, OSError):
                pass

    p = argparse.ArgumentParser(prog="terminal.py", description=f"{APP_NAME} : agrégateur de news façon terminal")
    p.add_argument("--port", type=int, default=8787, help="port local (défaut : 8787)")
    p.add_argument("--interval", type=int, default=180, help="secondes entre deux récupérations (défaut : 180, minimum 60)")
    p.add_argument("--sources", default=str(DEFAULT_SOURCES), help="fichier des sources (défaut : sources.json)")
    p.add_argument("--check", action="store_true", help="teste chaque source une fois puis quitte")
    p.add_argument("--build", metavar="DOSSIER", help="génère une version statique dans DOSSIER")
    p.add_argument("--previous", metavar="URL", help="avec --build : news.json en ligne à reprendre")
    p.add_argument("--no-browser", action="store_true", help="n'ouvre pas le navigateur au lancement")
    p.add_argument("--lan", action="store_true",
                   help="rend le terminal accessible aux appareils du même Wi-Fi (iPhone, iPad…)")
    args = p.parse_args(argv)

    sources = load_sources(Path(args.sources))
    interval = max(60, args.interval)

    if args.check:
        ssl_context()
        return run_check(Aggregator(sources, "check", interval))
    if args.build:
        return run_build(Aggregator(sources, "static", interval), Path(args.build), args.previous)
    ssl_context()  # chargé une fois avant les lectures en parallèle
    return run_server(Aggregator(sources, "local", interval), args.port, not args.no_browser, args.lan)


if __name__ == "__main__":
    sys.exit(main())
