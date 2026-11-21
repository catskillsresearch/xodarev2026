/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyVectorIncrementLaw
public import StochLean.Probability.Brownian.LevyCharacterization
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-! # Joint Gaussian processes from orthogonal martingale brackets

Finite-dimensional Gaussianity in both time and coordinate is deduced from
the proved joint increment laws and filtration independence. The zero initial
condition is explicit: continuous brackets alone permit random initial shifts.
-/

@[expose] public section

open MeasureTheory StochLean WithLp
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}
  (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
  (hd : ∀ i, Indistinguishable
    (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
  (ho : ∀ i j, i ≠ j → Indistinguishable
    (((hX i).isSemimartingale hF).continuousQuadraticCovariation
      ((hX j).isSemimartingale hF) hF) 0 P)

include hX hF hd ho

theorem hasLaw_pi_gaussian_increment_of_orthogonal {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω i ↦ X i t ω - X i s ω)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 (t - s))) P := by
  have hm : Measurable (fun ω i ↦ X i t ω - X i s ω) :=
    measurable_pi_iff.2 (fun i ↦ ((hX i).isSemimartingale hF).adapted.measurable.sub
      ((hX i).isSemimartingale hF).adapted.measurable)
  refine ⟨hm.aemeasurable, ?_⟩
  apply (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective
  rw [Measure.map_map (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable hm]
  exact (hasLaw_gaussian_vector_increment_of_orthogonal hX hF hd ho hst).map_eq

omit [Fintype ι]
variable [Finite ι]

theorem iIndepFun_increment_of_orthogonal {s t : ℝ≥0} (hst : s ≤ t) :
    iIndepFun (fun i ω ↦ X i t ω - X i s ω) P := by
  let := Fintype.ofFinite ι
  exact (iIndepFun_iff_hasLaw_pi_pi (fun i ↦
    (hX i).hasLaw_gaussian_increment_of_bracket_eq_time hF (hd i) hst)).2
      (hasLaw_pi_gaussian_increment_of_orthogonal hX hF hd ho hst)

theorem iIndepFun_eval_of_orthogonal (h0 : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) (t : ℝ≥0) :
    iIndepFun (fun i ↦ X i t) P := by
  apply (iIndepFun_increment_of_orthogonal hX hF hd ho
    (show (0 : ℝ≥0) ≤ t from zero_le)).congr
  intro i
  filter_upwards [h0 i] with ω hω
  simp [hω]

theorem hasIndepIncrements_vector_of_orthogonal :
    HasIndepIncrements (fun t ω ↦ (toLp 2 (fun i ↦ X i t ω) : EuclideanSpace ℝ ι)) P := by
  let := Fintype.ofFinite ι
  have ha : Adapted F (fun t ω ↦ (toLp 2 (fun i ↦ X i t ω) : EuclideanSpace ℝ ι)) := by
    intro t
    let : MeasurableSpace Ω := F t
    apply (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp
    exact measurable_pi_iff.2 (fun i ↦ ((hX i).isSemimartingale hF).adapted t)
  apply ha.hasIndepIncrements_of_indep_comap
  intro s t hst
  simpa only [← toLp_sub, Pi.sub_def] using
    indep_vector_increment_past_of_orthogonal hX hF hd ho hst

theorem isGaussianProcess_vector_of_orthogonal (h0 : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) :
    IsGaussianProcess (fun t ω ↦ (toLp 2 (fun i ↦ X i t ω) : EuclideanSpace ℝ ι)) P := by
  let := Fintype.ofFinite ι
  apply HasIndepIncrements.isGaussianProcess
  · intro t
    apply HasGaussianLaw.toLp_pi 2
    exact (iIndepFun_eval_of_orthogonal hX hF hd ho h0 t).hasGaussianLaw
      (fun i ↦ ((hX i).isBrownianReal_of_continuousBracket_eq_time
        hF (hd i) (h0 i)).toIsPreBrownianReal.hasLaw_eval t |>.hasGaussianLaw)
  · filter_upwards [ae_all_iff.2 h0] with ω hω
    change toLp 2 (fun i ↦ X i 0 ω) = (0 : EuclideanSpace ℝ ι)
    ext i
    exact hω i
  · exact hasIndepIncrements_vector_of_orthogonal hX hF hd ho

theorem isGaussianProcess_coordinate_time_of_orthogonal
    (h0 : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) :
    IsGaussianProcess (fun (p : (_i : ι) × ℝ≥0) ω ↦ X p.1 p.2 ω) P := by
  let := Fintype.ofFinite ι
  exact ((isGaussianProcess_vector_of_orthogonal hX hF hd ho h0).comp_right
    (fun p : (_i : ι) × ℝ≥0 ↦ p.2)).comp_left
      (fun p ↦ PiLp.proj 2 (fun _ : ι ↦ ℝ) p.1)

end ProbabilityTheory
