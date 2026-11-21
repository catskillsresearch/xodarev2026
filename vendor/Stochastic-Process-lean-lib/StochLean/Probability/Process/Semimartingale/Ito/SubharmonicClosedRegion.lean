/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.Subharmonic
public import StochLean.Probability.Process.LocalMartingale.RegionStopping
public import StochLean.ForMathlib.Analysis.LocalSmoothExtension
public import StochLean.Probability.Martingale.InitialMask

/-! # Subharmonic composition stopped inside a compact subregion

The actual smooth extension and patched stopped coordinates give a bounded
local submartingale, hence a true submartingale. The initial-event mask is
restored exactly. No global growth or initial-moment condition is imposed on
the original unmasked composition.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

theorem submartingale_masked_stopped_comp_laplacian_nonneg_on_compact
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D K : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ 2 f D) (hlap : ∀ x ∈ D, 0 ≤ Laplacian.laplacian f x)
    {c : EuclideanSpace ℝ ι} (hc : c ∈ K) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hstay : ∀ᵐ ω ∂P, 0 < τ ω → ∀ t,
      toLp 2 (fun i ↦ stoppedProcess (X i) τ t ω) ∈ K) :
    Submartingale (stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (fun ω ↦ f (toLp 2 (fun i ↦ X i t ω)))) τ) F P := by
  classical
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_extension_near_closed hK.isClosed hD hKD hf
  obtain ⟨Y, hY, hq, hcv, hmem, he, _⟩ := exists_region_patched_stopped_coordinates
    hX hF hτ (R := fun x ↦ toLp 2 x ∈ K) (fun i ↦ c i) hc hstay
  have hdY : ∀ i, Indistinguishable
      (((hY i).isSemimartingale hF).continuousQuadraticVariation hF) (stoppedProcess A τ) P :=
    fun i ↦ (hq i).trans ((hd i).stoppedProcess τ)
  have hoY : ∀ i j, i ≠ j → Indistinguishable
      (((hY i).isSemimartingale hF).continuousQuadraticCovariation
        ((hY j).isSemimartingale hF) hF) 0 P := by
    intro i j hij
    exact ((hcv i j).trans ((ho i j hij).stoppedProcess τ)).trans
      (Eventually.of_forall (fun _ _ ↦ rfl))
  have hG : Submartingale (fun t ω ↦ g (toLp 2 (fun i ↦ Y i t ω))) F P := by
    apply submartingale_comp_laplacian_nonneg_of_isotropic_of_integrable_envelope
      hY hF hdY hoY hg
    · filter_upwards [hmem] with ω hω t
      rw [(laplacian_congr_nhds (hgf _ (hω t))).eq_of_nhds]
      exact hlap _ (hKD (hω t))
    · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
      exact fun _ ↦ ⟨fun _ ↦ C, integrable_const C,
        hmem.mono (fun _ hω t _ ↦ hC _ (hω t))⟩
  have hGM := hG.indicator_initial (hτ.measurableSet_gt 0)
  have hEq : Indistinguishable
      (fun t ↦ {ω | 0 < τ ω}.indicator (fun ω ↦ g (toLp 2 (fun i ↦ Y i t ω))))
      (stoppedProcess
        (fun t ↦ {ω | 0 < τ ω}.indicator (fun ω ↦ f (toLp 2 (fun i ↦ X i t ω)))) τ) P := by
    filter_upwards [hmem] with ω hω t
    rw [stoppedProcess_indicator_comm]
    by_cases hp : 0 < τ ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < τ ω} from hp),
        indicator_of_mem (show ω ∈ {ω | 0 < τ ω} from hp), (hgf _ (hω t)).eq_of_nhds]
      simp only [he ω hp, MeasureTheory.stoppedProcess]
    · simp only [indicator_of_notMem (show ω ∉ {ω | 0 < τ ω} from hp)]
  apply hGM.congr _ hEq.ae_eq
  intro t
  have hcF : IsCompleteSubMeasurableSpace P (F t) :=
    fun S hS ↦ F.mono bot_le S (hF.complete_initial S hS)
  exact (hcF.measurable_congr_ae (hGM.stronglyAdapted.adapted t) (hEq.ae_eq t)).stronglyMeasurable

end ProbabilityTheory
