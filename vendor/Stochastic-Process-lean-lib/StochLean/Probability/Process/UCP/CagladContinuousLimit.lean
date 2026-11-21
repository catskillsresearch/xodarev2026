/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Complete
public import StochLean.Probability.Process.UCP.RightLimit
public import StochLean.Probability.Process.UCP.Algebra
public import StochLean.Probability.Process.Path.CagladUniformLimit
public import StochLean.Probability.Process.Measurability.RightLimit
public import StochLean.Probability.Process.Measurability.ContinuousVersion

/-! # Continuous UCP limits from caglad approximants

The actual right-limit processes inherit the UCP-Cauchy property on a
slightly enlarged horizon. Existing adapted cadlag UCP completeness supplies
their limit. A uniform right-increment error converging in measure transfers
UCP convergence back to the original caglad sequence, whose locally uniform
subsequence forces left continuity of that same limit.

The right-limit transformation is not asserted to be a modification. Its
error is controlled at all times, including zero. The final everywhere
continuous version reuses the existing initial-null-set reset construction;
no new UCP limit selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℕ → ℝ≥0 → Ω → ℝ} {R : ℕ → Ω → ℝ}

/-- A one-unit enlargement of the horizon transfers UCP-Cauchy control
to the actual right-limit processes. -/
theorem CauchyUCP.rightLimitProcess_of_caglad (hB : CauchyUCP P B)
    (hc : ∀ n, HasCagladPaths (B n) P) :
    CauchyUCP P (fun n ↦ rightLimitProcess (B n)) := by
  intro T ε hε η hη
  obtain ⟨N, hN⟩ := hB (T + 1) ε hε η hη
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  apply le_trans _ (hN m n hm hn)
  apply measure_mono_ae
  filter_upwards [hc m, hc n] with ω hmω hnω hω
  obtain ⟨t, ht, hgt⟩ := hω
  have hdev : ENNReal.ofReal ε < compactDeviation (B m) (B n) (T + 1) ω :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mpr hgt).trans_le
      ((enorm_sub_le_compactDeviation ht ω).trans
        (compactDeviation_rightLimitProcess_le hmω hnω T))
  simp only [compactDeviation, lt_iSup_iff] at hdev
  obtain ⟨s, hs, hsg⟩ := hdev
  exact ⟨s, hs, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hsg⟩

/-- A common-event uniform path bound converging in measure gives UCP
convergence to zero. No measurable uncountable supremum is assumed. -/
theorem tendstoUCP_zero_of_uniform_norm_bound_inMeasure
    (hR : TendstoInMeasure P R atTop 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖B n t ω‖ ≤ R n ω) :
    TendstoUCP P B atTop 0 := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have ht := tendstoInMeasure_iff_norm.mp hR ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hb n] with ω hω hmem
  obtain ⟨t, _, hgt⟩ := hmem
  simp only [Pi.zero_apply, sub_zero] at hgt ⊢
  exact (hgt.le.trans (hω t)).trans (le_abs_self _)

/-- Existing adapted cadlag UCP completeness, followed by a locally uniform
subsequence of the original caglad sequence, yields a continuous-path limit.
Only the right-increment error tends to zero in measure; no pathwise error
convergence or continuity certificate is an input. -/
theorem CauchyUCP.exists_adapted_continuous_limit_of_caglad [IsFiniteMeasure P]
    (hB : CauchyUCP P B) (ha : ∀ n, Adapted F (B n)) (hF : F.IsUsual P)
    (hc : ∀ n, HasCagladPaths (B n) P)
    (hR : TendstoInMeasure P R atTop 0)
    (hgap : ∀ n, ∀ᵐ ω ∂P, ∀ t,
      ‖rightLimitProcess (B n) t ω - B n t ω‖ ≤ R n ω) :
    ∃ A : ℝ≥0 → Ω → ℝ, Adapted F A ∧ HasContinuousPaths A P ∧
      TendstoUCP P B atTop A := by
  have hca : CauchyUCP P (fun n ↦ rightLimitProcess (B n)) :=
    hB.rightLimitProcess_of_caglad hc
  have hra : ∀ n, Adapted F (rightLimitProcess (B n)) :=
    fun n ↦ (ha n).rightLimitProcess_of_usual hF (hc n)
  have hrc : ∀ n, HasCadlagPaths (rightLimitProcess (B n)) P :=
    fun n ↦ (hc n).hasCadlagPaths_rightLimitProcess
  obtain ⟨A, hAa, hAc, hAr⟩ := hca.exists_adapted_cadlag_limit hra hF hrc
  have hE : TendstoUCP P (fun n ↦ rightLimitProcess (B n) - B n) atTop 0 :=
    tendstoUCP_zero_of_uniform_norm_bound_inMeasure hR hgap
  have hBA : TendstoUCP P B atTop A := by
    have h := hAr.sub hE
    simpa only [sub_sub_cancel, sub_zero] using h
  obtain ⟨k, _, hlu⟩ := hBA.exists_seq_ae_locallyUniform
  have hleft : HasLeftContinuousPaths A P := by
    filter_upwards [hlu, ae_all_iff.mpr hc] with ω hu hω
    exact isLeftContinuousPath_of_locallyUniform (fun n ↦ (hω (k n)).1)
      (fun T ↦ tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hu T))
  have hcont : HasContinuousPaths A P := by
    filter_upwards [hleft] with ω hl
    exact continuous_iff_continuousAt.mpr fun t ↦
      continuousAt_iff_continuous_left_right.mpr ⟨hl t, (hAc ω).1 t⟩
  exact ⟨A, hAa, hcont, hBA⟩

/-- The established continuous-version reset also gives an adapted limit
whose every path is continuous, without changing the UCP limit. -/
theorem CauchyUCP.exists_everywhere_continuous_limit_of_caglad [IsFiniteMeasure P]
    (hB : CauchyUCP P B) (ha : ∀ n, Adapted F (B n)) (hF : F.IsUsual P)
    (hc : ∀ n, HasCagladPaths (B n) P)
    (hR : TendstoInMeasure P R atTop 0)
    (hgap : ∀ n, ∀ᵐ ω ∂P, ∀ t,
      ‖rightLimitProcess (B n) t ω - B n t ω‖ ≤ R n ω) :
    ∃ A : ℝ≥0 → Ω → ℝ, Adapted F A ∧ (∀ ω, Continuous (A · ω)) ∧
      TendstoUCP P B atTop A := by
  obtain ⟨Y, hYa, hYc, hBY⟩ := hB.exists_adapted_continuous_limit_of_caglad ha hF hc hR hgap
  obtain ⟨A, he, hAp, hAc⟩ :=
    hYa.stronglyAdapted.exists_continuous_indistinguishable_of_usual hF hYc
  exact ⟨A, hAp.stronglyAdapted.adapted, hAc, hBY.congr_right he⟩

end ProbabilityTheory
