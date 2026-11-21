#!/usr/bin/env python3
"""Ensure every SignatureVolatility/**/*.lean is @import-ed from Writeup exactly once."""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "SignatureVolatility"
WRITEUP = ROOT / "Writeup"
IMPORT_RE = re.compile(r'@import\s+"([^"]+\.lean)"')


def main() -> int:
    all_leans = {
        p.resolve().relative_to(LEAN_DIR.resolve()).as_posix()
        for p in LEAN_DIR.rglob("*.lean")
    }
    occ: dict[str, list[str]] = defaultdict(list)
    for md in WRITEUP.rglob("*.md"):
        for rel in IMPORT_RE.findall(md.read_text(encoding="utf-8")):
            target = (md.parent / rel).resolve()
            try:
                lean_rel = target.relative_to(LEAN_DIR.resolve()).as_posix()
            except ValueError:
                print(f"OUTSIDE: {md.relative_to(ROOT)} imports {rel}", file=sys.stderr)
                continue
            occ[lean_rel].append(md.relative_to(ROOT).as_posix())

    missing = sorted(all_leans - set(occ))
    extra = sorted(set(occ) - all_leans)
    dupes = {k: v for k, v in occ.items() if len(v) > 1}

    ok = not missing and not extra and not dupes
    print(
        f"SignatureVolatility/**/*.lean: {len(all_leans)}; "
        f"Writeup @imports: {sum(len(v) for v in occ.values())} "
        f"({len(occ)} unique)"
    )
    if missing:
        print("MISSING:")
        for m in missing:
            print(f"  {m}")
    if dupes:
        print("DUPLICATES:")
        for k, v in sorted(dupes.items()):
            print(f"  {k}")
            for p in v:
                print(f"    {p}")
    if extra:
        print("EXTRA (no such lean):")
        for e in extra:
            print(f"  {e}")
    if ok:
        print("OK: each lean file is included exactly once")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
