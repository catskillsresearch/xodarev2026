module

public import SignatureVolatility.TheoremB
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDuality


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper Theorem B: the `←` direction and the full iff are false

Paper Theorem B claimed, under H1–H3, a martingale price, NFLVR, special-semimartingale
signature coordinates, and the affine / Riccati iff for every finitely supported `u₀` with
finite signature transform. The first three clauses and the `→` direction of the iff are true
(`theorem_B_mp`). The `←` direction is false as a universal statement, so the full conjunction
is false.

These negations hang off `not_affine_riccati_duality_mpr` / `not_affine_riccati_duality`. They
introduce no `sorry` and no added assumptions. `R_op` is the paper operator `riccatiOp`, as it
was in the dropped `signatureRiccatiKit_of_setup`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The paper's `←` direction of Theorem B's Riccati clause is false as a statement over all
finitely supported `u₀` with finite signature transform. This is the same claim as
`not_affine_riccati_duality_mpr`; the `HypH3` hypothesis of the old wrapper is unused. -/
theorem not_theorem_B_mpr (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (_h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ¬ ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
      SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω)) |
            (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
              ((paperSetup B M.hT).W_hat t ω)) :=
  fun h => not_affine_riccati_duality_mpr M B h

/-- The paper's Theorem B is false: its conjunction includes the universal Riccati iff, which
fails. The martingale, NFLVR and special-semimartingale clauses are true (`theorem_B_mp`); the
failure is only the `←` direction of the iff. -/
theorem not_theorem_B (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (_h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ¬ ∃ sol : SignaturePriceSolution M (paperSetup B M.hT)
          (itoCalculusKit_of_mathfin B M.hT),
        (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
          Integrable (sol.S t) P ∧
          P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
        SatisfiesNFLVR P (AdmissibleGainsUnderP P) ∧
        (∀ I : Word (M.d + 1),
          Nonempty (IsSpecialSemimartingale P (paperSetup B M.hT).signatureFiltration M.T
            (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) ∧
        (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
          SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
          ((∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
              ∀ t ∈ Icc 0 M.T,
                Integrable (fun ω => Real.exp (dualPairing u₀.1
                    ((paperSetup B M.hT).W_hat M.T ω))) P ∧
                P[fun ω => Real.exp (dualPairing u₀.1
                    ((paperSetup B M.hT).W_hat M.T ω)) |
                  (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
                  fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
                    ((paperSetup B M.hT).W_hat t ω))) ↔
            Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1))) := by
  intro h
  obtain ⟨_sol, _hmart, _hnflvr, _hsemi, hiff⟩ := h
  exact not_affine_riccati_duality M B hiff

end SignatureVolatility
