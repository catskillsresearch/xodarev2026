module

public import SignatureVolatility.SignatureRiccatiKit.CoordSemimartingale
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# The `←` direction of the affine / Riccati duality

The `→` direction is proved in `affine_riccati_duality_mp`
(`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMp`).
Here `affine_riccati_duality_mpr` states the `←` direction at paper strength with `sorry` (the
single `sorry` of the repository), `affine_riccati_duality` assembles the paper's equivalence, and
`signatureRiccatiKit_of_setup` builds the paper-strength Riccati kit from it.

`R_op` is pinned to the paper's operator `riccatiOp` (Definition 18; agrees with
`riccatiOpBounded N` on `𝒟_fin`, see `riccatiOp_eq_bounded`). For the time-extended Brownian
signature this is the generator / carré-du-champ field of paper Definition 2.18:
`ℛ(u) = u|₀ + ½ Σᵢ u|ᵢᵢ + ½ Σᵢ (u|ᵢ) ⧢ (u|ᵢ)`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Affine / Riccati duality, `←` direction (paper Theorem 4.2(ii), p. 21; proof §4.4, p. 23). OPEN — `sorry`.**

For finitely supported `u₀` with finite signature transform, the conditional transform is
exponential-affine, `𝔼[exp⟨u₀, Ŵ_T⟩ | ℱ_t] = exp⟨ψ(T − t), Ŵ_t⟩` for a classical solution `ψ` of
`∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, iff a global classical Riccati solution exists. Transform finiteness is
imposed per initial datum (the paper's "for all `u₀ ∈ 𝒟_fin`" can never hold for Brownian
signatures: `u₀ = c e₁₁` gives `𝔼 exp(c W_t² / 2) = ∞` once `c t ≥ 1`).

This is the `←` direction (the `→` direction is `affine_riccati_duality_mp`, proved): a positive
local martingale `exp⟨ψ(T − t), Ŵ_t⟩` must be shown to be the
true conditional expectation. **The paper's justification is unsupported.** §4.4 asserts that
"the finite-coordinate moment estimates and H3 give the uniform-integrability bound", but H3
(p. 12) is a Novikov bound on the price volatility `⟨ℓ, Ŵ⟩` and polynomial moments (Prop. 2.12)
do not give uniform integrability of an exponential. The passage to `T_w` (Lemma 4.10, p. 25) uses
the local Lipschitz estimate of Lemma B.2 / 2.20 and the shuffle estimate B.1, both false
(`not_lemma78_local_lipschitz`, `not_lemma77_shuffle_estimate`).

Status: open problem. No counterexample was found (one-letter solutions satisfy it by the classical
Widder theorem). The closest literature, Cuchiero–Svaluto-Ferro–Teichmann, *Signature SDEs from an
affine and polynomial perspective*, arXiv:2302.01362, Thm 3.5 / Remark 3.6, assumes the
true-martingale property rather than proving it. -/
theorem affine_riccati_duality_mpr (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)) :
    SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
    Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
    ∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
        P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω)) := by
  sorry

/-- **Affine / Riccati duality** (paper Theorem 4.2(ii)), the paper's equivalence: `→` is
`affine_riccati_duality_mp` (proved), `←` is the open `affine_riccati_duality_mpr`. -/
theorem affine_riccati_duality (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)) :
    SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
    ((∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
        P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) :=
  fun h => ⟨affine_riccati_duality_mp M B u₀ h, affine_riccati_duality_mpr M B u₀ h⟩

/-- **Paper goal.** Riccati kit over the paper-strength Brownian prolonged setup. -/
noncomputable def signatureRiccatiKit_of_setup (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    SignatureRiccatiKit Ω P M (paperSetup B M.hT) where
  coord_special_semimartingale := fun I => isSpecialSemimartingale_paperSig2_coeff B I M.hT
  R_op := riccatiOp
  affine_riccati_duality := affine_riccati_duality M B

end SignatureVolatility
