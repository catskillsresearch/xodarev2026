# Theorem B — EMM / NFLVR and Riccati duality

@import "TheoremB_ailean.txt" {code_block=false}

Paper: Xodarev Theorem B. Under H1–H3:

1. $S$ is a true $(\mathcal F^{\widehat W}_t,\mathbb P)$-martingale on $[0,T]$;
2. NFLVR holds for admissible gains;
3. every finite signature coordinate is a special semimartingale;
4. nonempty classical Riccati solutions are equivalent to the exponential-affine conditional transform representation.

The proved entry point is `theorem_B_mp` (martingale, Delbaen–Schachermayer NFLVR for the genuine $L^2$ Itô cone `BoundedBelowGains` of uniformly bounded-below strategies of a continuous version of the packaged solution — $HS\sigma$ in $\mathcal{F}^W$-predictable $L^2$, wealth a continuous genuine $L^2$ Itô integral against $W^0$, narrower than the paper's local class — special-semimartingale coordinates, and the forward Riccati direction). Clause (3) is stated with `Nonempty (IsSpecialSemimartingale …)` because the Lean object is a structure, not a `Prop`. The compared theorem `theorem_B_mp_unwrapped` asserts the same four conjuncts for an `IsSignaturePrice` process $S$ itself, so the NFLVR statement is for $S$. The paper's full Theorem B (including the converse iff) is false; see `not_theorem_B`. Literal NFLVR and the terminal-only bound are refuted for Black–Scholes; see the narrative with the main results.

@import "../../SignatureVolatility/TheoremB.lean"

**The converse direction is false.** The false theorem `affine_riccati_duality_mpr` has been removed. Its negation `not_affine_riccati_duality_mpr` is assembled in the counterexample development; `not_theorem_B_mpr` and `not_theorem_B` hang off it. All are proved and compared. The argument is due to Gemini Carbon and is narrated with the main results.
