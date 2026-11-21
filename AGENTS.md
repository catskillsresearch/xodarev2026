# Agent notes (xodarev2026)

## After a successful `lake build` of a module

In the **same turn**:

1. **Shake** the file: drop unused `open` / `open scoped` / `noncomputable` / redundant imports; keep the minimal preamble that still builds cleanly (no new errors/warnings).
2. Re-run `lake build` on that module if the shake changed anything.
3. Add its short id to `VERIFIED` in `scripts/build_holes.py`.
4. Run `python3 scripts/build_holes.py`.

Do not mark verified on a failed or incomplete build.

## Shakes vs the holes dependency graph

**Shake** = minimal Lean imports that still build (transitive imports are omitted).

**Holes board** = one node per file under `SignatureVolatility/`, edges from **direct**
`import SignatureVolatility…` only. The root barrel `SignatureVolatility.lean` is **not**
part of the graph (it imports every submodule and creates a useless star). The HTML graph
also **transitively reduces** edges for layout; open/blocked status still uses every direct
import.

If you want a dependency to show on the board, keep or add a direct `import` for it even
when Lean would get it transitively.
