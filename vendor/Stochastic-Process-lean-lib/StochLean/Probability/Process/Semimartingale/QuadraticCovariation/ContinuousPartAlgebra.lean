/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPart

/-! # Bilinearity of continuous covariation

The common-event raw identities and absolutely summable jump series give the
algebraic identities. No varying-integrator UCP continuity principle is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_comm
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF)
      (hY.continuousQuadraticCovariation hX hF) P := by
  have heq : Indistinguishable (X + Y) (Y + X) P :=
    ae_of_all _ fun ω t ↦ add_comm (X t ω) (Y t ω)
  filter_upwards [(hX.add hY).continuousQuadraticVariation_congr (hY.add hX) hF heq]
    with ω hω t
  simp only [continuousQuadraticCovariation, hω t]
  ring

theorem IsSemimartingale.continuousQuadraticCovariation_self
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation hX hF)
      (hX.continuousQuadraticVariation hF) P := by
  filter_upwards [hX.quadraticCovariation_continuous_jump_decomposition hX hF,
    hX.quadraticVariation_continuous_jump_decomposition hF, hX.quadraticCovariation_self hF]
    with ω hmix hx hraw t
  have hm := (hmix t).2
  rw [hraw t] at hm
  simp only [← pow_two] at hm
  linarith [(hx t).2]

theorem IsSemimartingale.continuousQuadraticCovariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hX' : IsSemimartingale X' F P) (hY' : IsSemimartingale Y' F P) (hF : F.IsUsual P)
    (hXX' : Indistinguishable X X' P) (hYY' : Indistinguishable Y Y' P) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF)
      (hX'.continuousQuadraticCovariation hY' hF) P := by
  have hsum : Indistinguishable (X + Y) (X' + Y') P := by
    filter_upwards [hXX', hYY'] with ω hx hy t
    simp only [Pi.add_apply, hx t, hy t]
  filter_upwards [(hX.add hY).continuousQuadraticVariation_congr (hX'.add hY') hF hsum,
    hX.continuousQuadraticVariation_congr hX' hF hXX',
    hY.continuousQuadraticVariation_congr hY' hF hYY'] with ω hsumω hx hy t
  simp only [continuousQuadraticCovariation, hsumω t, hx t, hy t]

theorem IsSemimartingale.continuousQuadraticCovariation_add_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.add hY).continuousQuadraticCovariation hZ hF)
      (hX.continuousQuadraticCovariation hZ hF + hY.continuousQuadraticCovariation hZ hF) P := by
  filter_upwards [(hX.add hY).quadraticCovariation_continuous_jump_decomposition hZ hF,
    hX.quadraticCovariation_continuous_jump_decomposition hZ hF,
    hY.quadraticCovariation_continuous_jump_decomposition hZ hF,
    hX.quadraticCovariation_add_left hY hZ hF, hX.hasCadlagPaths, hY.hasCadlagPaths]
    with ω hsum hx hy hraw hcx hcy t
  have hj : (∑' s : Ioc 0 t, jumpProcess (X + Y) s ω * jumpProcess Z s ω) =
      (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Z s ω) +
        (∑' s : Ioc 0 t, jumpProcess Y s ω * jumpProcess Z s ω) := by
    calc
      _ = ∑' s : Ioc 0 t,
          (jumpProcess X s ω * jumpProcess Z s ω + jumpProcess Y s ω * jumpProcess Z s ω) := by
        apply tsum_congr
        intro s
        rw [hcx.jumpProcess_add hcy s, add_mul]
      _ = _ := (hx t).1.of_abs.tsum_add (hy t).1.of_abs
  have h := (hsum t).2
  rw [hraw t, hj] at h
  simp only [Pi.add_apply] at h ⊢
  linarith [(hx t).2, (hy t).2]

theorem IsSemimartingale.continuousQuadraticCovariation_const_mul_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable ((hX.const_mul c).continuousQuadraticCovariation hY hF)
      (c • hX.continuousQuadraticCovariation hY hF) P := by
  filter_upwards [(hX.const_mul c).quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.quadraticCovariation_const_mul_left hY hF c, hX.hasCadlagPaths]
    with ω hc hx hraw hcx t
  have hj : (∑' s : Ioc 0 t, jumpProcess (fun u v ↦ c * X u v) s ω * jumpProcess Y s ω) =
      c * (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) := by
    calc
      _ = ∑' s : Ioc 0 t, c * (jumpProcess X s ω * jumpProcess Y s ω) := by
        apply tsum_congr
        intro s
        rw [hcx.jumpProcess_const_mul c s]
        ring
      _ = _ := (hx t).1.of_abs.tsum_mul_left c
  have h := (hc t).2
  rw [hraw t, hj] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
  linear_combination c * (hx t).2 - h

theorem IsSemimartingale.continuousQuadraticCovariation_add_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation (hY.add hZ) hF)
      (hX.continuousQuadraticCovariation hY hF + hX.continuousQuadraticCovariation hZ hF) P := by
  filter_upwards [hX.continuousQuadraticCovariation_comm (hY.add hZ) hF,
    hY.continuousQuadraticCovariation_add_left hZ hX hF,
    hY.continuousQuadraticCovariation_comm hX hF, hZ.continuousQuadraticCovariation_comm hX hF]
    with ω hsum hadd hy hz t
  simp only [hsum t, hadd t, Pi.add_apply, hy t, hz t]

theorem IsSemimartingale.continuousQuadraticCovariation_const_mul_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable (hX.continuousQuadraticCovariation (hY.const_mul c) hF)
      (c • hX.continuousQuadraticCovariation hY hF) P := by
  filter_upwards [hX.continuousQuadraticCovariation_comm (hY.const_mul c) hF,
    hY.continuousQuadraticCovariation_const_mul_left hX hF c,
    hY.continuousQuadraticCovariation_comm hX hF] with ω hcomm hmul hxy t
  simp only [hcomm t, hmul t, Pi.smul_apply, smul_eq_mul, hxy t]

end ProbabilityTheory
