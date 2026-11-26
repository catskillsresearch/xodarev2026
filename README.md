[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/xodarev2026/build.yml?label=Lean%204)](https://github.com/catskillsresearch/xodarev2026/actions/workflows/build.yml)
[![Palomar](https://img.shields.io/badge/Palomar-2026--11--26--000043-0f766e.svg)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000043&version=1)

# Formal Verification and Counterexamples for Signature Volatility Models

Formalization of Akmal Xodarev,
*On the Structural Foundations of Signature Volatility Models*,
arXiv:2605.17142.

Standalone package. This repo is registered with
[Palomar](https://palomar-registry.org/about) on its own as
[PALOMAR-2026-11-26-000043](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000043&version=1),
version 1 (see `PROVENANCE.md`).

## Build

```bash
lake exe cache get   # optional, after lake update
lake build
```

Toolchain: Lean `v4.35.0` (see `lean-toolchain`), Mathlib pin in `lakefile.toml`.

## Layout

| Path | Content |
|------|---------|
| `sources/` | Source paper |
| `SignatureVolatility/` | Library modules |
| `SignatureVolatilityComparator/` | Palomar Challenge and Solution |
| `Writeup/` | Mathematical writeup sources |
| `SignatureVolatility.pdf` | Rebuilt report |
| `vendor/` | formal-mathfin, brownian-motion, and the pinned Palomar policy |

## Writeup

The paper-facing report is [`SignatureVolatility.md`](SignatureVolatility.md), built as [`SignatureVolatility.pdf`](SignatureVolatility.pdf).

```bash
bash scripts/build_arxiv_pdf.sh   # → SignatureVolatility.pdf
```

The live proof-hole board is [`holes.html`](holes.html) (`python3 scripts/build_holes.py`; `scripts/serve_holes.sh`).

## Palomar packaging

| File | Role |
|------|------|
| [`SignatureVolatilityComparator/Challenge.lean`](SignatureVolatilityComparator/Challenge.lean) | Mathlib-only statement of record (`sorry` holes) |
| [`SignatureVolatilityComparator/Solution.lean`](SignatureVolatilityComparator/Solution.lean) | Imports the library; proves the Challenge theorems |
| [`comparator.json`](comparator.json) | Eleven unwrapped theorems |
| [`formalization.yaml`](formalization.yaml) | Palomar project metadata |
| [`PROVENANCE.md`](PROVENANCE.md) | Provenance and registration |

Registry entry: [PALOMAR-2026-11-26-000043](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000043&version=1), version 1.
