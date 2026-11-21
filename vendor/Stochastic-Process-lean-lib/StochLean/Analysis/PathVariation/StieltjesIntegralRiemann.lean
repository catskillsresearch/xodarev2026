/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepApproximation
public import StochLean.Analysis.PathVariation.StieltjesIntegralSimple
public import StochLean.Analysis.PathVariation.StieltjesIntegralContinuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Left Riemann sums for pathwise Stieltjes integrals

The partial terminal cell is included, and the initial term is retained. Uniform
convergence holds on the whole horizon for continuous integrands, even when the
locally BV integrator has jumps. No nested-partition hypothesis is needed.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

noncomputable def stieltjesLeftSum (π : TimePartition T) (x f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f 0 * x 0 + ∑ i : Fin π.size,
    f (π.left i) * (x (min (π.right i) t) - x (min (π.left i) t))

theorem stieltjesLeftSum_terminal (π : TimePartition T) (x f : ℝ≥0 → ℝ) :
    stieltjesLeftSum π x f T = f 0 * x 0 + ∑ i : Fin π.size, f (π.left i) * π.increment x i := by
  simp only [stieltjesLeftSum, TimePartition.increment, TimePartition.left, TimePartition.right,
    min_eq_left (π.point_le_horizon _)]

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem integrableOn_variationStieltjes_leftStep (π : TimePartition T) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn (π.leftStep f) (Ioc 0 t) (totalVariationStieltjes x hx hr).measure :=
  integrableOn_variationStieltjes_finite_step π.left π.right (fun i ↦ f (π.left i)) (f 0) t

theorem pathStieltjesIntegral_leftStep (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pathStieltjesIntegral x hx hr (π.leftStep f) = stieltjesLeftSum π x f := by
  funext t
  exact pathStieltjesIntegral_finite_step π.left π.right (fun i ↦ f (π.left i))
    π.left_le_right (f 0) t

theorem integrableOn_variationStieltjes_of_continuousOn {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) :
    IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure :=
  hf.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    measure_Ioc_lt_top.ne

theorem tendstoUniformlyOn_stieltjesLeftSum {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ stieltjesLeftSum (π n) x f)
      (pathStieltjesIntegral x hx hr f) atTop (Icc 0 T) := by
  have h := tendstoUniformlyOn_pathStieltjesIntegral
    (fun n ↦ integrableOn_variationStieltjes_leftStep (x := x) (hx := hx) (hr := hr) (π n) f T)
    (integrableOn_variationStieltjes_of_continuousOn hf)
    (TimePartition.tendstoUniformlyOn_leftStep hf hmesh)
  simpa only [pathStieltjesIntegral_leftStep] using h

theorem tendsto_stieltjesLeftSum_terminal {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f 0 * x 0 + ∑ i : Fin (π n).size, f ((π n).left i) * (π n).increment x i)
      atTop (𝓝 (pathStieltjesIntegral x hx hr f T)) := by
  have h := (tendstoUniformlyOn_stieltjesLeftSum (x := x) (hx := hx) (hr := hr) hf hmesh).tendsto_at
    (show T ∈ Icc 0 T from ⟨bot_le, le_rfl⟩)
  simpa only [stieltjesLeftSum_terminal] using h

end StochLean
