/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FiniteCoordinateDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Iterated coordinate derivatives agree with the Frechet Hessian

The first index is the outer derivative and the second index is the
inner derivative. No symmetry argument is needed for this identity.
-/

@[expose] public section

namespace StochLean

theorem coordinateDeriv_coordinateDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : ι) (x : ι → ℝ) :
    coordinateDeriv (coordinateDeriv f j) i x = coordinateSecondDeriv f i j x := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have h := (hd.differentiable (by decide) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (Pi.single j 1) x)
  change fderiv ℝ (fun y ↦ fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)
  rw [h.fderiv]
  simp

end StochLean
