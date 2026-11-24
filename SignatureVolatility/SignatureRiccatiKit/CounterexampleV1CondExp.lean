module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.BrownianScalingShiftedExponent
public import SignatureVolatility.SignatureRiccatiKit.CondExpMulIndepDisintegrate
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.DualPairing


/-!
# B5. Conditional-expectation factorisation

For every `λ ≥ 1`, at `t = T - λ^{-2/3}(T/2)`,
`𝔼[M_T^(λ) | ℱ_t] = M_t^(λ) * v₁(λ^{1/3} W_t)` a.s.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B5.** Conditional-expectation factorisation of the Doléans exponential
against `v₁`. -/
lemma counterexampleV1_condExp (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ lam : ℝ, 1 ≤ lam →
      let s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
      let t_lam := M.T - s_lam
      P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
          ((paperSetup B M.hT).W_hat M.T ω)) |
        (paperSetup B M.hT).signatureFiltration.σAlg t_lam] =ᵐ[P]
        fun ω =>
          Real.exp (dualPairing (counterexampleU0 M.hd lam)
            ((paperSetup B M.hT).W_hat t_lam ω)) *
          counterexampleV1AtHalf M B
            (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩) := by
  intro lam hlam s_lam t_lam
  have hlam_pos : 0 < lam := by linarith
  have hs_pos : 0 < s_lam :=
    mul_pos (Real.rpow_pos_of_pos hlam_pos _) (half_pos M.hT)
  have hs_le : s_lam ≤ M.T / 2 := by
    have h1 : lam ^ (-(2 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlam (by norm_num)
    have hT : 0 ≤ M.T / 2 := le_of_lt (half_pos M.hT)
    simpa [s_lam] using mul_le_of_le_one_left hT h1
  have ht0 : 0 ≤ t_lam := by
    have : s_lam ≤ M.T := le_trans hs_le (div_le_self (le_of_lt M.hT) one_le_two)
    linarith
  have htT : t_lam < M.T := by linarith
  have h := condExp_mul_indep_disintegrate M B hlam ht0 htT
  have htime : lam ^ (2 / 3 : ℝ) * (M.T - t_lam) = M.T / 2 := by
    simp only [t_lam, s_lam, sub_sub_cancel, ← mul_assoc, ← Real.rpow_add hlam_pos,
      add_neg_cancel, Real.rpow_zero, one_mul]
  simpa only [htime, counterexampleV1AtHalf] using h

end SignatureVolatility
