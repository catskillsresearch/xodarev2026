# Abstract

Xodarev gives four structural theorems for signature volatility models on the weighted tensor algebra $T_w$: global existence and uniqueness of the strong solution of $dS_t = S_t\langle\ell,\widehat W_t\rangle\,dB_t$ under hypotheses H1–H3 (Theorem A); an asset-pricing / NFLVR theorem on the prolonged-signature filtration, separated from Riccati transform non-explosion (Theorem B); a characterisation of market completeness on the price filtration by density of truncated signature spans, with minimal depth $N_S^\ast(\ell,w)$ (Theorem C); and the Galtchouk–Kunita–Watanabe hedging-error decomposition with a quantitative weight-tail bound on residual signature levels (Theorem D).

This formalization checks the paper’s definitions and main theorems in Lean 4 / Mathlib. The Lean library `SignatureVolatility` follows the paper’s theorem chain. All **94** file-level modules on the holes board are verified, with **no `sorry`** in the inventory (`sorryCount = 0`). The board is the file-level dependency graph under [`SignatureVolatility/`](../SignatureVolatility/); regenerate with `python3 scripts/build_holes.py` and view [`holes.html`](../holes.html).

Source paper: Xodarev [@xodarev2026] (arXiv:2605.17142v1). AI assistance is acknowledged at the end with model cards for Google Gemini Carbon, Composer 2.5, and Cursor Auto.
