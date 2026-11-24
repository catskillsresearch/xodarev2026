module

public import SignatureVolatility.TheoremB
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDuality


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper Theorem B: `←` part (open) and the full statement

`theorem_B_mp` (`SignatureVolatility/TheoremB.lean`) is the proved part. `theorem_B_mpr` is the
`←` direction of the Riccati transform equivalence (paper Theorem B / Theorem 4.2(ii)); it is
`affine_riccati_duality_mpr`, the single open `sorry` of the repository. `theorem_B` is the full
paper statement, proved from `theorem_B_mp` and `theorem_B_mpr`; its Riccati operator is that of
the paper-strength kit `signatureRiccatiKit_of_setup` (definitionally `riccatiOp`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B, `←` direction of the Riccati clause. OPEN** (via
`affine_riccati_duality_mpr`, `sorry`). If the Riccati equation `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, has a
global classical solution, the conditional signature transform of `u₀` is exponential-affine. -/
theorem theorem_B_mpr (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (_h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
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
  fun u₀ hf hn => affine_riccati_duality_mpr M B u₀ hf hn

/-- **Paper Theorem B** (full statement): martingale property, NFLVR, special-semimartingale
coordinates, and the Riccati transform equivalence of part (ii), with `ℛ` the operator of the
paper-strength kit `signatureRiccatiKit_of_setup`. Proved from `theorem_B_mp` and the open
`theorem_B_mpr`. -/
theorem theorem_B (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ (sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT)),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) P ∧
        P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
      SatisfiesNFLVR P (AdmissibleGainsUnderP P) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale P
          (paperSetup B M.hT).signatureFiltration M.T
          (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
        ((∃ rSol : ClassicalRiccatiSolution M.w M.T
            (signatureRiccatiKit_of_setup M B).R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω)) |
              (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
                ((paperSetup B M.hT).W_hat t ω))) ↔
        Nonempty (ClassicalRiccatiSolution M.w M.T
          (signatureRiccatiKit_of_setup M B).R_op u₀.1))) := by
  obtain ⟨sol, hmart, hnflvr, hsemi, hmp⟩ := theorem_B_mp M B h3
  exact ⟨sol, hmart, hnflvr, hsemi,
    fun u₀ hf => ⟨hmp u₀ hf, theorem_B_mpr M B h3 u₀ hf⟩⟩

end SignatureVolatility
