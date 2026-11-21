# Introduction

This formalization reconstructs Xodarev’s structural theory of signature volatility models [@xodarev2026] in Lean 4, using Mathlib. The Lean library `SignatureVolatility` follows the paper’s order: weighted tensor algebra and prolonged Brownian signature → Theorems A–D → concrete models (Black–Scholes, first-order Brownian vol, Heston level 2, Quintic OU, geometric signature).

**Status.** Every module under [`SignatureVolatility/`](../SignatureVolatility/) is listed as verified on the holes board ([`HOLES.md`](../HOLES.md), [`holes.html`](../holes.html)): **94 done · 0 open · 0 blocked · `sorryCount = 0`**.

**Faithfulness note (filtrations).** The paper separates three filtrations: the Brownian filtration $\mathcal F^W$, the prolonged-signature filtration $\mathcal F^{\widehat W}$ (equal to $\mathcal F^W$ after time augmentation), and the price filtration $\mathcal F^S$, which is generally smaller. Completeness (Theorem C) and the GKW residual (Theorem D) are stated on $\mathcal F^S$, not as full Brownian-filtration claims. Lean mirrors that split via `signatureFiltration` / `brownianFiltration` / `priceFiltration` and the equality lemma `signature_filtration_eq_brownian_filtration`.

**Architectural identity.** Theorems A–D form a chain: stochastic-exponential well-posedness and $L^2$ control (A) feed NFLVR and Riccati duality (B); the EMM and signature grading feed completeness depth (C); depth feeds the residual split in the hedging-error theorem (D).

- [Sources and tooling](Introduction/SourcesAndTooling.md)
- [How to read this writeup](Introduction/HowToReadThisWriteup.md)
