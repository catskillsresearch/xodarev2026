# Why the `←` affine / Riccati duality fails (paper Thm 4.2(ii); Theorem B's Riccati clause)

**Lean:** `not_affine_riccati_duality_mpr`
(`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean`), with
corollaries `not_affine_riccati_duality` (`SignatureRiccatiKit/AffineRiccatiDuality.lean`),
`not_theorem_B_mpr` and `not_theorem_B` (`TheoremBMpr.lean`). Axioms: `propext`,
`Classical.choice`, `Quot.sound`. All four are in `comparator.json`.

**What Lean proves.** `not_affine_riccati_duality_mpr` takes any model `M` (so `d ≥ 1`, `T > 0`,
`s₀ > 0`, and the model's `HypH1`, `HypH2`, and parameter nondegeneracy `ℓ ≠ 0`) and any
Brownian driver `B`. There is no analytic `HypH3` hypothesis. It concludes that the paper's
universal `←` claim is false: it is not the case that every finitely supported `u₀` with finite
signature transform and some global classical Riccati solution admits a classical solution `ψ`
for which
`E[exp⟨u₀, Ŵ_T⟩ | ℱ_t] = exp⟨ψ(T − t), Ŵ_t⟩ holds almost surely for all `t ∈ [0, T]`.
`not_affine_riccati_duality` is the corresponding negation of the iff, under the same
hypotheses (every model and driver, no `HypH3`). `not_theorem_B_mpr` and `not_theorem_B` are
the same `←` failure and the failure of the paper's full Theorem B conjunction; each carries
an additional unused `HypH3` hypothesis, so those two apply to every model and driver for which
analytic `HypH3` holds. `HypH3` is satisfiable: it holds for constant volatility (Black–Scholes).

**The counterexample.** Let `1` be the first space letter and `0` the time letter. For `λ ≥ 1`, set
`u₀^(λ) = 2λ e_[1,1,1] − λ e_[1,0] − 12λ² e_[1,1,1,1,0]`. Lean proves:

- `riccatiOp_counterexampleU0`: `ℛ(u₀^(λ)) = 0` identically, so `ψ ≡ u₀^(λ)` is a global
  classical Riccati solution;
- `ae_dualPairing_counterexampleU0_eq`: almost surely,
  `⟨u₀^(λ), Ŵ_t⟩ = (λ/3) W_t³ − λ∫₀ᵗ W_r dr − (λ²/2)∫₀ᵗ W_r⁴ dr`, where `W` is the first
  Brownian coordinate;
- `lintegral_exp_counterexampleU0_pairing_le_one` and
  `signatureTransformFinite_counterexampleU0`: `∫ exp⟨u₀^(λ), Ŵ_t⟩ dP ≤ 1` for `t ∈ [0, T]`,
  so the signature transform is finite.

Thus both hypotheses of the universal `←` claim hold for each `u₀^(λ)`. Lean does not state a
theorem that `exp⟨u₀^(λ), Ŵ_t⟩` is a local martingale, nor a theorem that it is not a true
martingale. The compared conclusion is only that the universal conditional-expectation formula
fails.

At `t_λ = T − λ^(−2/3)·(T/2)`, `counterexampleV1_condExp` gives, via Brownian scaling,

`E[exp⟨u₀^(λ), Ŵ_T⟩ | ℱ_{t_λ}] = exp⟨u₀^(λ), Ŵ_{t_λ}⟩ · v₁(λ^(1/3) W_{t_λ})`.

Here `v₁` is one fixed function for which Lean proves:

- `0 < v₁ ≤ 1` and `v₁(x) → 0` as `x → +∞` (`counterexampleV1_pos_le`,
  `counterexampleV1_tendsto_zero`);
- `log v₁` has a quartic lower bound (`counterexampleV1_log_bound`);
- `log v₁` is nonpositive (`counterexampleV1_log_nonpos`).

**Why the conclusion fails.** The `←` claim allows any solution `ψ`, not only `ψ ≡ u₀^(λ)`.
Suppose it held for every `λ ≥ 1`. Then `log v₁(λ^(1/3) W_{t_λ}) = ⟨ψ(T − t_λ) − u₀^(λ), Ŵ_{t_λ}⟩`.
A pairing with an element of `T_w` that depends only on `W_t` is, almost everywhere, an entire
function of exponential type ≤ 1. So `log v₁` agrees almost everywhere with an entire function of
type ≤ `λ^(−1/3)`. These functions are equal for every `λ`, so one entire function has
exponential type 0 and quartic growth on `ℝ`.

By Phragmén–Lindelöf and Liouville, that function is a polynomial of degree ≤ 4. On `(−∞, 0]` it
is nonpositive and has at most logarithmic decay, so it is constant. But `v₁ → 0` at `+∞`, which
rules out a constant. A single `λ` would not suffice: exponential type 1 alone does not exclude an
arbitrary `ψ`. The scaled family is what forces type 0.

**Literature (cited by Carbon, see appendix).** Abi Jaber–Gassiat–Sotnikov,
arXiv:2503.17103 (strict local martingales in signature volatility models; checked by Carbon,
not independently re-verified here). Abi Jaber–Attal–Sotnikov, arXiv:2606.29622 (**not
verified** by us). These references are not Lean theorems.

**Source material.** The verbatim Gemini "Carbon" narrative and Lean blueprint, as pasted by Lars
Warren Ericson on 2026-11-24, is in
[`appendix/carbon_affine_riccati_duality_mpr.md`](appendix/carbon_affine_riccati_duality_mpr.md).
The Lean route above follows it. It differs in packaging: Girsanov-free pieces, and pillars
A–D split across `SignatureRiccatiKit/*` modules.
