# Introduction

This formalization reconstructs Xodarev’s structural theory of signature volatility models [@xodarev2026] in Lean 4, using Mathlib. The Lean library `SignatureVolatility` follows the paper’s order: weighted tensor algebra and prolonged Brownian signature → Theorems A–D → concrete models (Black–Scholes, first-order Brownian vol, Heston level 2, Quintic OU, geometric signature).

**Status.** Every module under [`SignatureVolatility/`](../SignatureVolatility/) is listed as verified on the holes board ([`HOLES.md`](../HOLES.md), [`holes.html`](../holes.html)): **208 done · 0 open · 0 blocked · `sorryCount = 0`**. There are 211 first-party `.lean` files in all, counting the root barrel `SignatureVolatility.lean` and the Palomar Challenge and Solution. Palomar registration: TBD. The official description and the claim-to-Lean strength table are in [Palomar registration and main results](PalomarRegistration.md).

**Faithfulness note (filtrations).** The paper separates three filtrations: the Brownian filtration $\mathcal F^W$, the prolonged-signature filtration $\mathcal F^{\widehat W}$ (equal to $\mathcal F^W$ after time augmentation), and the price filtration $\mathcal F^S$, which is generally smaller. Completeness (Theorem C) and the GKW residual (Theorem D) are stated on $\mathcal F^S$, not as full Brownian-filtration claims. Lean mirrors that split via `signatureFiltration` / `brownianFiltration` / `priceFiltration` and the equality lemma `signature_filtration_eq_brownian_filtration`.

**What the paper presents as a chain, and what Lean does with it.** The paper organises Theorems A–D as a chain: stochastic-exponential well-posedness (A) feeds NFLVR and Riccati duality (B); completeness depth (C) is stated on the price filtration; depth feeds the residual split in the hedging-error theorem (D). Lean proves Theorem A and the GKW projection part of Theorem D at the strength recorded in the Palomar table; it proves the forward fragment `theorem_B_mp` of Theorem B, and it refutes the paper's full Theorem B conjunction, the `←` affine/Riccati duality, Theorem C, Proposition 58, Theorem D's residual hypothesis (for Black–Scholes), and Lemmas 77 and 78, each at the exact strength of the corresponding `not_X` theorem. Nothing is left open.

- [Sources and tooling](Introduction/SourcesAndTooling.md)
- [How to read this writeup](Introduction/HowToReadThisWriteup.md)
- [Library root barrel](Introduction/LibraryRoot.md)
