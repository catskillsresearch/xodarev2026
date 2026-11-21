/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Measurability
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.VariationBound
public import StochLean.Probability.Process.Path.FiniteVariation

/-! # Adapted cadlag finite-variation processes are semimartingales

Protter II.7 follows directly from the pathwise elementary-integral bound. The random
variation need not be integrable. This does not yet construct a Stieltjes measure or the
general Chapter II integral.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- A common-event finite pathwise operator bound suffices. Neither measurability nor
integrability of the bound `R` is needed, since convergence is first proved pathwise. -/
theorem isGoodIntegrator_of_ae_elementaryIntegral_bound (R : Ω → ℝ)
    (hmeas : ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      AEStronglyMeasurable (hH.elementaryIntegral X) P)
    (hb : ∀ᵐ ω ∂P, 0 ≤ R ω ∧
      ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F, ∀ C : ℝ, 0 ≤ C →
        (∀ t ω, ‖H t ω‖ ≤ C) → ‖hH.elementaryIntegral X ω‖ ≤ C * R ω) :
    IsGoodIntegrator X F P := by
  intro H hH hu
  apply tendstoInMeasure_of_tendsto_ae (fun n ↦ hmeas (H n) (hH n))
  filter_upwards [hb] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε / (R ω + 1) := div_pos hε (by linarith [hω.1])
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu _ hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbound : ∀ t v, ‖H n t v‖ ≤ ε / (R ω + 1) := by
    intro t v
    simpa only [dist_zero_left] using (hN n hn (t, v)).le
  have h := hω.2 (H n) (hH n) _ hδ.le hbound
  change dist ((hH n).elementaryIntegral X ω) 0 < ε
  rw [dist_zero_right]
  apply h.trans_lt
  have heq : ε / (R ω + 1) * (R ω + 1) = ε := div_mul_cancel₀ ε (by linarith [hω.1])
  nlinarith

theorem HasFiniteTotalVariationPaths.isGoodIntegrator (hf : HasFiniteTotalVariationPaths X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    IsGoodIntegrator X F P := by
  apply isGoodIntegrator_of_ae_elementaryIntegral_bound
    (fun ω ↦ ‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) univ).toReal)
    (fun _ hH ↦ (hH.measurable_elementaryIntegral ha hF hr).aestronglyMeasurable)
  filter_upwards [hf] with ω hω
  refine ⟨by positivity, fun H hH C hC hb ↦ ?_⟩
  exact hH.choose.norm_integral_le_totalVariation hC (by simpa only [hH.choose_spec] using hb) ω hω

theorem HasFiniteTotalVariationPaths.isTotalSemimartingale (hf : HasFiniteTotalVariationPaths X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsTotalSemimartingale X F P :=
  ⟨ha, hc, hf.isGoodIntegrator ha hF hc.hasRightContinuousPaths⟩

theorem HasFiniteVariationPaths.isSemimartingale (hf : HasFiniteVariationPaths X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsSemimartingale X F P := by
  intro T
  change IsTotalSemimartingale (stoppedProcess X (FiniteStoppingTime.const F T).withTop) F P
  rw [FiniteStoppingTime.stoppedProcess_eq]
  have hstop : Adapted F (fun t ↦ X (min t T)) :=
    fun t ↦ (ha _).mono (F.mono (min_le_left t T)) le_rfl
  have hcad : HasCadlagPaths (fun t ↦ X (min t T)) P := hc.mono (fun _ h ↦ h.min_const T)
  refine ⟨hstop, hcad, ?_⟩
  apply isGoodIntegrator_of_ae_elementaryIntegral_bound
    (fun ω ↦ ‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) (Icc 0 T)).toReal)
    (fun _ hH ↦
      (hH.measurable_elementaryIntegral hstop hF hcad.hasRightContinuousPaths).aestronglyMeasurable)
  filter_upwards [hasFiniteVariationPaths_iff_ae_forall_horizon.mp hf] with ω hω
  refine ⟨by positivity, fun H hH C hC hb ↦ ?_⟩
  exact hH.choose.norm_integral_min_const_le_variation hC
    (by simpa only [hH.choose_spec] using hb) ω T (hω T)

end ProbabilityTheory
