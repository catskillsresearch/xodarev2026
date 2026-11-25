# Why the `←` affine / Riccati duality fails (paper Thm 4.2(ii); Theorem B's Riccati clause)

**Lean:** `not_affine_riccati_duality_mpr`
(`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean`), with
corollaries `not_affine_riccati_duality` (`SignatureRiccatiKit/AffineRiccatiDuality.lean`),
`not_theorem_B_mpr` and `not_theorem_B` (`TheoremBMpr.lean`). Axioms: `propext`,
`Classical.choice`, `Quot.sound`. All four are in `comparator.json`.

**What Lean proves.** Take any model `M` (any `d ≥ 1`, `T > 0`, any admissible weight `w`) and any
Brownian driver `B`. Then the paper's universal claim is false. That claim says: for every
finitely supported `u₀` with finite signature transform, if a global classical Riccati solution
exists, then some solution `ψ` gives `E[exp⟨u₀, Ŵ_T⟩ | ℱ_t] = exp⟨ψ(T − t), Ŵ_t⟩` on `[0, T]`.
Since the `←` direction fails, so do the paper's iff and the full Theorem B conjunction.
`not_theorem_B_mpr` and `not_theorem_B` carry the H3 hypothesis only to match the paper, and do
not use it. H3 is satisfiable: it holds for constant volatility (Black–Scholes).

**The counterexample.** Let `1` be the first space letter and `0` the time letter. For `λ ≥ 1`, set
`u₀^(λ) = 2λ e_[1,1,1] − λ e_[1,0] − 12λ² e_[1,1,1,1,0]`. Then:

- `ℛ(u₀^(λ)) = 0` exactly, so `ψ ≡ u₀^(λ)` is a global classical Riccati solution.
- Almost surely, `⟨u₀^(λ), Ŵ_t⟩ = λ∫₀ᵗ W² dW − (λ²/2)∫₀ᵗ W⁴ dr`, where `W` is the first Brownian
  coordinate. So `exp⟨u₀^(λ), Ŵ_t⟩` is the Doléans exponential of `∫ λW² dW`, and
  `E exp⟨u₀^(λ), Ŵ_t⟩ ≤ 1` (supermartingale bound). The signature transform is therefore finite,
  and both hypotheses of the claim hold.

This exponential is a positive local martingale but not a true martingale. At
`t_λ = T − λ^(−2/3)·T/2`, Lean computes, via Brownian scaling,

`E[exp⟨u₀^(λ), Ŵ_T⟩ | ℱ_{t_λ}] = exp⟨u₀^(λ), Ŵ_{t_λ}⟩ · v₁(λ^(1/3) W_{t_λ})`.

Here `v₁` is one fixed function with three properties:

- `0 < v₁ ≤ 1` and `v₁(x) → 0` as `x → +∞`;
- `log v₁` has a quartic lower bound;
- `log v₁` has a logarithmic lower bound on `(−∞, 0]`.

**Why the conclusion fails.** The conclusion allows any solution `ψ`, not only `ψ ≡ u₀^(λ)`.
Suppose it held for every `λ ≥ 1`. Then `log v₁(λ^(1/3) W_{t_λ}) = ⟨ψ(T − t_λ) − u₀^(λ), Ŵ_{t_λ}⟩`.
A pairing with an element of `T_w` that depends only on `W_t` is, almost everywhere, an entire
function of exponential type ≤ 1. So `log v₁` agrees almost everywhere with an entire function of
type ≤ `λ^(−1/3)`. These functions are equal for every `λ`, so one entire function has
exponential type 0 and quartic growth on `ℝ`.

By Phragmén–Lindelöf and Liouville, that function is a polynomial of degree ≤ 4. On `(−∞, 0]` it
lies between `−c − 2 log(1 + (T/2)|x|)` and `0`, so it is constant. But `v₁ → 0` at `+∞`, which
rules out a constant. A single `λ` would not suffice: exponential type 1 alone does not exclude an
arbitrary `ψ`. The scaled family is what forces type 0.

**Literature (cited by Carbon, see appendix).** Abi Jaber–Gassiat–Sotnikov,
arXiv:2503.17103 (strict local martingales in signature volatility models; checked by Carbon,
not independently re-verified here). Abi Jaber–Attal–Sotnikov, arXiv:2606.29622 (**not
verified** by us).

**Source material.** The verbatim Gemini "Carbon" narrative and Lean blueprint, as pasted by Lars
Warren Ericson on 2026-11-24, is in
[`appendix/carbon_affine_riccati_duality_mpr.md`](appendix/carbon_affine_riccati_duality_mpr.md).
The Lean route above follows it. It differs in packaging: Girsanov-free pieces, and pillars
A–D split across `SignatureRiccatiKit/*` modules.
