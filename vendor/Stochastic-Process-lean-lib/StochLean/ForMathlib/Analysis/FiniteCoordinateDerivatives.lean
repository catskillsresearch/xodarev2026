/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Normed.Group.Real

/-! # Coordinate derivatives of finite real vectors

Coordinates are evaluations of Mathlib's Frechet derivatives on the standard
basis. The identities expand the existing linear and bilinear maps exactly.
-/

@[expose] public section

open Finset

namespace StochLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuousLinearMap_apply_eq_sum_single (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem continuousBilinearMap_apply_eq_sum_single
    (L : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (v w : ι → ℝ) :
    L v w = ∑ i, ∑ j, L (Pi.single i 1) (Pi.single j 1) * v i * w j := by
  have h := continuousLinearMap_apply_eq_sum_single (L.flip w) v
  simp only [ContinuousLinearMap.flip_apply] at h
  rw [h]
  apply sum_congr rfl
  intro i _
  rw [continuousLinearMap_apply_eq_sum_single (L (Pi.single i 1)) w, sum_mul]
  apply sum_congr rfl
  intro j _
  ring

noncomputable def coordinateDeriv (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

noncomputable def coordinateSecondDeriv (f : (ι → ℝ) → ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)

theorem fderiv_apply_eq_sum_coordinateDeriv (f : (ι → ℝ) → ℝ) (x v : ι → ℝ) :
    fderiv ℝ f x v = ∑ i, coordinateDeriv f i x * v i :=
  continuousLinearMap_apply_eq_sum_single _ _

theorem second_fderiv_apply_eq_sum_coordinateSecondDeriv
    (f : (ι → ℝ) → ℝ) (x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = ∑ i, ∑ j, coordinateSecondDeriv f i j x * v i * w j :=
  continuousBilinearMap_apply_eq_sum_single _ _ _

theorem contDiff_coordinateDeriv {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : ι) :
    ContDiff ℝ 1 (coordinateDeriv f i) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  exact hd.clm_apply contDiff_const

theorem continuous_coordinateSecondDeriv {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (i j : ι) : Continuous (coordinateSecondDeriv f i j) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hH : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by decide)
  exact ((hH.clm_apply contDiff_const).clm_apply contDiff_const).continuous

end StochLean
