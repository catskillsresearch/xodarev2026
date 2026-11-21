/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.Harmonic
public import StochLean.Probability.Process.LocalMartingale.RegionStopping
public import StochLean.Probability.Process.Semimartingale.UsualCongruence
public import StochLean.ForMathlib.Analysis.LocalSmoothExtension

/-! # Harmonic composition localized inside a closed subregion

A genuine globally C2 extension is constructed. On the initial zero-stopping
branch, the coordinates are first shifted to a point in the region, which
leaves their continuous brackets unchanged. The final process restores the
source initial-event mask. No global smoothness of the input is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

theorem isContinuousLocalMartingale_masked_stopped_comp_harmonic_on_closed
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D K : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hK : IsClosed K) (hKD : K ⊆ D)
    (hf : HarmonicOnNhd f D) {c : EuclideanSpace ℝ ι} (hc : c ∈ K)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hstay : ∀ᵐ ω ∂P, 0 < τ ω → ∀ t,
      toLp 2 (fun i ↦ stoppedProcess (X i) τ t ω) ∈ K) :
    IsContinuousLocalMartingale (stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (fun ω ↦ f (toLp 2 (fun i ↦ X i t ω)))) τ) F P := by
  classical
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_extension_near_closed hK hD hKD hf.contDiffOn
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
  have hG : IsContinuousLocalMartingale
      (fun t ω ↦ g (toLp 2 (fun i ↦ Y i t ω))) F P := by
    apply isContinuousLocalMartingale_comp_of_isotropic_trace_zero_on_paths hY hF hdY hoY
      (hg.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff)
    filter_upwards [hmem] with ω hω t
    change (∑ i, coordinateSecondDeriv (fun x ↦ g (toLp 2 x)) i i (fun j ↦ Y j t ω)) = 0
    rw [sum_coordinateSecondDeriv_toLp_eq_laplacian hg,
      (laplacian_congr_nhds (hgf _ (hω t))).eq_of_nhds]
    exact (hf _ (hKD (hω t))).2.eq_of_nhds
  have hGM : IsContinuousLocalMartingale
      (fun t ↦ {ω | 0 < τ ω}.indicator (fun ω ↦ g (toLp 2 (fun i ↦ Y i t ω)))) F P := by
    refine ⟨hG.1.indicator_initial (hτ.measurableSet_gt 0), ?_⟩
    filter_upwards [hG.2] with ω hω
    by_cases hp : 0 < τ ω
    · simpa only [indicator_of_mem (show ω ∈ {ω | 0 < τ ω} from hp)] using hω
    · simp only [indicator_of_notMem (show ω ∉ {ω | 0 < τ ω} from hp)]
      exact continuous_const
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
  exact hGM.congr hF ((hGM.isSemimartingale hF).congr_of_usual hF hEq).adapted hEq

end ProbabilityTheory
