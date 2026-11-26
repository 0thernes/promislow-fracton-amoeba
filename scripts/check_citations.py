#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Live citation & retraction audit for paper/references.bib (Playbook v1.3 Pass 5)."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from urllib.parse import quote

import requests

ROOT = Path(__file__).resolve().parents[1]


def parse_bib_entries(bib_text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    chunks = re.split(r"\n(?=@\w+\{)", bib_text.strip())
    for chunk in chunks:
        m_key = re.match(r"@(\w+)\{([^,]+),", chunk.strip())
        if not m_key:
            continue
        entry: dict[str, str] = {"type": m_key.group(1), "key": m_key.group(2).strip()}
        for field in ("title", "doi", "eprint", "url", "year", "author"):
            m = re.search(rf"\b{field}\s*=\s*\{{((?:[^{{}}]|\{{[^{{}}]*\}})*)\}}", chunk, re.IGNORECASE)
            if m:
                entry[field] = re.sub(r"\s+", " ", m.group(1)).strip()
        entries.append(entry)
    return entries


def verify_entry(entry: dict[str, str], offline: bool = False) -> tuple[bool, str]:
    key = entry["key"]
    doi = entry.get("doi", "").strip()
    eprint = entry.get("eprint", "").strip()
    url = entry.get("url", "").strip()

    if not (doi or eprint or url):
        return False, f"[{key}] missing doi/eprint/url identifier"

    if offline:
        return True, f"[{key}] structural identifier present (offline mode)"

    headers = {"User-Agent": "promislow-fracton-amoeba/1.0.0 (mailto:0_0@0thernes.art)"}

    if doi:
        cr_url = f"https://api.crossref.org/works/{quote(doi, safe='')}"
        try:
            r = requests.get(cr_url, headers=headers, timeout=15)
            if r.status_code != 200:
                return False, f"[{key}] Crossref HTTP {r.status_code} for DOI {doi}"
            msg = r.json().get("message", {})
            # Check Crossref retraction / update-to flags
            for upd in msg.get("update-to", []):
                if "retract" in str(upd.get("type", "")).lower():
                    return False, f"[{key}] RETRACTED per Crossref update-to ({doi})"
            cr_title = " ".join(msg.get("title", [])).lower()
            if "retracted:" in cr_title or "retraction:" in cr_title:
                return False, f"[{key}] RETRACTED title detected ({doi})"
            return True, f"[{key}] Crossref OK ({doi})"
        except (requests.RequestException, ValueError) as exc:
            return False, f"[{key}] Crossref request error for {doi}: {exc}"

    if eprint:
        ax_url = f"https://export.arxiv.org/api/query?id_list={quote(eprint, safe='')}"
        try:
            r = requests.get(ax_url, headers=headers, timeout=15)
            if r.status_code != 200 or "<entry>" not in r.text:
                return False, f"[{key}] arXiv API lookup failed for {eprint}"
            if "withdrawn" in r.text.lower() and "this paper has been withdrawn" in r.text.lower():
                return False, f"[{key}] WITHDRAWN arXiv paper ({eprint})"
            return True, f"[{key}] arXiv API OK ({eprint})"
        except requests.RequestException as exc:
            return False, f"[{key}] arXiv API error for {eprint}: {exc}"

    try:
        r = requests.head(url, headers=headers, allow_redirects=True, timeout=15)
        if r.status_code >= 400:
            r = requests.get(url, headers=headers, allow_redirects=True, timeout=15)
        if r.status_code >= 400:
            return False, f"[{key}] URL HTTP {r.status_code} ({url})"
        return True, f"[{key}] URL HTTP {r.status_code} OK ({url})"
    except requests.RequestException as exc:
        return False, f"[{key}] URL error for {url}: {exc}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", action="store_true", help="Check structure without network calls")
    args = ap.parse_args()

    bib_path = ROOT / "paper" / "references.bib"
    if not bib_path.exists():
        print(f"ERROR: missing {bib_path}", file=sys.stderr)
        return 1

    entries = parse_bib_entries(bib_path.read_text(encoding="utf-8"))
    if not entries:
        print("ERROR: no BibTeX entries parsed", file=sys.stderr)
        return 1

    failures = 0
    for entry in entries:
        ok, msg = verify_entry(entry, offline=args.offline)
        print(("PASS " if ok else "FAIL ") + msg)
        if not ok:
            failures += 1

    print(f"\nChecked {len(entries)} BibTeX references: {len(entries) - failures} passed, {failures} failed.")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
