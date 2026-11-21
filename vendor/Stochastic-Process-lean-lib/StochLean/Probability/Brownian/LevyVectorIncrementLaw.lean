/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyLinearProjections
public import StochLean.Probability.Independence.ConditionalCharacteristicHilbert
public import StochLean.ForMathlib.Probability.GaussianVectorCharacteristic

/-! # Joint Gaussian increments from orthogonal brackets

The joint law is the canonical finite product of centered real Gaussian
laws, transported to Euclidean space. Its identification uses every linear
projection's conditional characteristic function, not an assumed Gaussian law.
-/

@[expose] public section

open MeasureTheory StochLean WithLp
open scoped NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}

theorem condExp_inner_characteristic_vector_increment_of_orthogonal
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P) {s t : ℝ≥0} (hst : s ≤ t)
    (u : EuclideanSpace ℝ ι) :
    P[fun ω ↦ Complex.exp (Complex.ofReal
      ⟪(toLp 2 (fun i ↦ X i t ω - X i s ω) : EuclideanSpace ℝ ι), u⟫ * Complex.I) | F s] =ᵐ[P]
      fun _ ↦ charFun ((Measure.pi (fun _ : ι ↦ gaussianReal 0 (t - s))).map (toLp 2)) u := by
  have h := condExp_characteristic_linearCombination_of_orthogonal Finset.univ
    hX hF (fun i ↦ u i) hd ho hst
  have he : (fun ω ↦ Complex.exp (Complex.ofReal
      ⟪(toLp 2 (fun i ↦ X i t ω - X i s ω) : EuclideanSpace ℝ ι), u⟫ * Complex.I)) =
      (fun ω ↦ Complex.exp (Complex.I * Complex.ofReal
        (∑ i, u i * (X i t ω - X i s ω)))) := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have hν : charFun ((Measure.pi (fun _ : ι ↦ gaussianReal 0 (t - s))).map (toLp 2)) u =
      Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * (∑ i, (u i) ^ 2)) * ((t : ℝ) - s))) := by
    rw [charFun_pi_centered_gaussian, NNReal.coe_sub hst]
  rw [he]
  simpa only [hν] using h

theorem hasLaw_gaussian_vector_increment_of_orthogonal
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ (toLp 2 (fun i ↦ X i t ω - X i s ω) : EuclideanSpace ℝ ι))
      ((Measure.pi (fun _ : ι ↦ gaussianReal 0 (t - s))).map (toLp 2)) P := by
  apply hasLaw_of_condExp_inner_characteristic (F.le s)
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp (measurable_pi_iff.2 (fun i ↦
      ((hX i).isSemimartingale hF).adapted.measurable.sub
        ((hX i).isSemimartingale hF).adapted.measurable)))
  exact condExp_inner_characteristic_vector_increment_of_orthogonal hX hF hd ho hst

omit [Fintype ι] in
theorem indep_vector_increment_past_of_orthogonal [Finite ι]
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (toLp 2 (fun i ↦ X i t ω - X i s ω) : EuclideanSpace ℝ ι)) inferInstance) P := by
  let := Fintype.ofFinite ι
  apply indep_comap_of_condExp_inner_characteristic
    (ν := (Measure.pi (fun _ : ι ↦ gaussianReal 0 (t - s))).map (toLp 2)) (F.le s)
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp (measurable_pi_iff.2 (fun i ↦
      ((hX i).isSemimartingale hF).adapted.measurable.sub
        ((hX i).isSemimartingale hF).adapted.measurable)))
  exact condExp_inner_characteristic_vector_increment_of_orthogonal hX hF hd ho hst

end ProbabilityTheory
