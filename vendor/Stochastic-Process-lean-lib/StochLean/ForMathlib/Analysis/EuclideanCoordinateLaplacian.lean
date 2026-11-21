/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FiniteCoordinateDerivatives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Coordinate Hessians and Mathlib's Euclidean Laplacian

The project coordinate derivatives on the finite sup-norm function space are
transported through the canonical Euclidean continuous linear equivalence.
Their diagonal sum is Mathlib's Laplacian, not a separately defined operator.
-/

@[expose] public section

open WithLp InnerProductSpace Laplacian

namespace StochLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {f : EuclideanSpace ℝ ι → ℝ}

theorem coordinateSecondDeriv_toLp (hf : ContDiff ℝ 2 f) (i j : ι) (x : ι → ℝ) :
    coordinateSecondDeriv (fun y ↦ f (toLp 2 y)) i j x =
      iteratedFDeriv ℝ 2 f (toLp 2 x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap
  calc
    _ = iteratedFDeriv ℝ 2 (f ∘ L) x ![Pi.single i 1, Pi.single j 1] := by
      rw [iteratedFDeriv_two_apply]
      rfl
    _ = _ := by
      rw [L.iteratedFDeriv_comp_right hf x (by decide),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1
      ext k
      fin_cases k <;> rfl

theorem sum_coordinateSecondDeriv_toLp_eq_laplacian
    (hf : ContDiff ℝ 2 f) (x : ι → ℝ) :
    (∑ i, coordinateSecondDeriv (fun y ↦ f (toLp 2 y)) i i x) = Δ f (toLp 2 x) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun ι ℝ)]
  simp only [coordinateSecondDeriv_toLp hf, EuclideanSpace.basisFun_apply]

theorem sum_coordinateSecondDeriv_toLp_eq_zero_of_harmonic
    (hf : HarmonicOnNhd f Set.univ) (x : ι → ℝ) :
    (∑ i, coordinateSecondDeriv (fun y ↦ f (toLp 2 y)) i i x) = 0 := by
  rw [sum_coordinateSecondDeriv_toLp_eq_laplacian (contDiffOn_univ.mp hf.contDiffOn)]
  exact (hf _ (Set.mem_univ _)).2.eq_of_nhds

end StochLean
