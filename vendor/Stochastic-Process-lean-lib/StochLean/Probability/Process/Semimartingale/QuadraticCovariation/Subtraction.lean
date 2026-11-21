/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra
public import StochLean.Probability.Process.Semimartingale.Subtraction

/-! # Subtraction in the canonical raw and continuous covariations -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_sub_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.sub hY).quadraticCovariation hZ hF)
      (hX.quadraticCovariation hZ hF - hY.quadraticCovariation hZ hF) P := by
  have he : Indistinguishable ((X - Y) + Y) X P :=
    Eventually.of_forall fun _ _ ↦ sub_add_cancel _ _
  have hz : Indistinguishable Z Z P := Eventually.of_forall fun _ _ ↦ rfl
  filter_upwards [(hX.sub hY).quadraticCovariation_add_left hY hZ hF,
    ((hX.sub hY).add hY).quadraticCovariation_congr hZ hX hZ hF he hz]
      with ω ha hc t
  exact eq_sub_iff_add_eq.mpr ((ha t).symm.trans (hc t))

theorem IsSemimartingale.quadraticCovariation_sub_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation (hY.sub hZ) hF)
      (hX.quadraticCovariation hY hF - hX.quadraticCovariation hZ hF) P := by
  filter_upwards [hX.quadraticCovariation_comm (hY.sub hZ) hF,
    hY.quadraticCovariation_sub_left hZ hX hF,
    hY.quadraticCovariation_comm hX hF, hZ.quadraticCovariation_comm hX hF]
      with ω hc hs hy hz t
  simp only [hc t, hs t, Pi.sub_apply, hy t, hz t]

theorem IsSemimartingale.continuousQuadraticCovariation_sub_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.sub hY).continuousQuadraticCovariation hZ hF)
      (hX.continuousQuadraticCovariation hZ hF -
        hY.continuousQuadraticCovariation hZ hF) P := by
  have he : Indistinguishable ((X - Y) + Y) X P :=
    Eventually.of_forall fun _ _ ↦ sub_add_cancel _ _
  have hz : Indistinguishable Z Z P := Eventually.of_forall fun _ _ ↦ rfl
  filter_upwards [(hX.sub hY).continuousQuadraticCovariation_add_left hY hZ hF,
    ((hX.sub hY).add hY).continuousQuadraticCovariation_congr hZ hX hZ hF he hz]
      with ω ha hc t
  exact eq_sub_iff_add_eq.mpr ((ha t).symm.trans (hc t))

theorem IsSemimartingale.continuousQuadraticCovariation_sub_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation (hY.sub hZ) hF)
      (hX.continuousQuadraticCovariation hY hF -
        hX.continuousQuadraticCovariation hZ hF) P := by
  filter_upwards [hX.continuousQuadraticCovariation_comm (hY.sub hZ) hF,
    hY.continuousQuadraticCovariation_sub_left hZ hX hF,
    hY.continuousQuadraticCovariation_comm hX hF,
    hZ.continuousQuadraticCovariation_comm hX hF] with ω hc hs hy hz t
  simp only [hc t, hs t, Pi.sub_apply, hy t, hz t]

end ProbabilityTheory
