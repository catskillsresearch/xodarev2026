module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.LintegralExpShifted
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto

/-!
# B1. Positivity and the unit upper bound for `v₁`

`0 < v₁ x ≤ 1` for every real `x`. This is the exponential supermartingale
bound `lintegral_exp_shiftedExponent_le_one` transferred from the
Doléans lintegral to the Bochner expectation that defines `v₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped ENNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma continuous_W_coord_v1 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (ω : Ω) :
    Continuous fun s : ℝ => MultiBrownian.W B s ω k :=
  (B.pathContinuous k ω).comp continuous_real_toNNReal

private lemma measurable_intervalIntegral_addW {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k := by
  have hsum : ∀ n : ℕ, Measurable fun ω =>
      ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      ((MultiBrownian.W_meas B _ k).const_add x).mul_const _
  have hlim : ∀ ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k)) := fun ω =>
    tendsto_lebRiemann_of_continuousOn hs
      (continuous_const.add (continuous_W_coord_v1 B k ω)).continuousOn
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

private lemma measurable_intervalIntegral_addW_pow4 {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4 := by
  have hsum : ∀ n : ℕ, Measurable fun ω =>
      ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) ^ 4 *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      (((MultiBrownian.W_meas B _ k).const_add x).pow_const 4).mul_const _
  have hlim : ∀ ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) ^ 4 *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4)) := fun ω =>
    tendsto_lebRiemann_of_continuousOn hs
      ((continuous_const.add (continuous_W_coord_v1 B k ω)).pow 4).continuousOn
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

private lemma measurable_counterexampleV1Exponent {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => counterexampleV1Exponent B hd s x ω := by
  have hW : Measurable fun ω => MultiBrownian.W B s ω ⟨0, hd⟩ :=
    MultiBrownian.W_meas B s ⟨0, hd⟩
  have hI := measurable_intervalIntegral_addW B ⟨0, hd⟩ hs x
  have hQ := measurable_intervalIntegral_addW_pow4 B ⟨0, hd⟩ hs x
  simp only [counterexampleV1Exponent]
  exact (((hW.const_add x).pow_const 3).sub measurable_const).const_mul _ |>.sub hI |>.sub
    (hQ.const_mul _)

/-- **B1.** `0 < v₁ x ≤ 1` for all `x`. -/
lemma counterexampleV1_pos_le (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (x : ℝ) :
    0 < counterexampleV1AtHalf M B x ∧ counterexampleV1AtHalf M B x ≤ 1 := by
  have hs : 0 ≤ M.T / 2 := div_nonneg M.hT.le (by norm_num)
  have hlint : ∫⁻ ω, ENNReal.ofReal
      (Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω)) ∂P ≤ 1 :=
    lintegral_exp_shiftedExponent_le_one B M.hd hs x
  have hmeas : Measurable fun ω =>
      Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω) :=
    Real.measurable_exp.comp (measurable_counterexampleV1Exponent B M.hd hs x)
  have hint : Integrable (fun ω =>
      Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω)) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have he : ∫⁻ ω, ‖Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω)‖ₑ ∂P =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω)) ∂P :=
      lintegral_congr fun ω => Real.enorm_eq_ofReal (Real.exp_pos _).le
    rw [HasFiniteIntegral, he]
    exact hlint.trans_lt ENNReal.one_lt_top
  constructor
  · have hpos : 0 < ∫ ω, Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω) ∂P := by
      refine (integral_pos_iff_support_of_nonneg
        (fun ω => (Real.exp_pos _).le) hint).mpr ?_
      have hsupp : Function.support (fun ω =>
          Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω)) = Set.univ := by
        ext ω; simp [(Real.exp_pos _).ne']
      rw [hsupp, measure_univ]; exact zero_lt_one
    simpa [counterexampleV1AtHalf, counterexampleV1] using hpos
  · have hle : ∫ ω, Real.exp (counterexampleV1Exponent B M.hd (M.T / 2) x ω) ∂P ≤ 1 := by
      rw [← ENNReal.ofReal_le_ofReal_iff zero_le_one,
        ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun _ => (Real.exp_pos _).le)]
      simpa using hlint
    simpa [counterexampleV1AtHalf, counterexampleV1] using hle

end SignatureVolatility
