# Agent notes (xodarev2026)

## After a successful `lake build` of a module

In the **same turn**:

1. **Shake** the file: drop unused `open` / `open scoped` / `noncomputable` / redundant imports; keep the minimal preamble that still builds cleanly (no new errors/warnings).
2. Re-run `lake build` on that module if the shake changed anything.
3. Add its short id to `VERIFIED` in `scripts/build_holes.py`.
4. Run `python3 scripts/build_holes.py`.

Do not mark verified on a failed or incomplete build.
