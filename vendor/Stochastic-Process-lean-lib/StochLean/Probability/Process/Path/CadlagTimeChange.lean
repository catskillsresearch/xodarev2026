/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.Topology.Order.LeftRightLim

/-! # Continuous monotone clocks for monotone real paths

A continuous monotone clock preserves right continuity: its image of a
right-hand ray stays in the corresponding right-hand ray of the original
path. For a real monotone path the resulting monotonicity supplies finite
left limits. This does not assert that arbitrary continuous time changes
preserve cadlag paths, and does not introduce a new clock or path owner.
-/

@[expose] public section

open Set
open scoped NNReal Topology

namespace ProbabilityTheory

/-- A monotone right-continuous real path remains cadlag under a continuous
monotone clock. The left limits follow from real monotonicity, not from an
unrestricted time-composition principle for cadlag paths. -/
theorem IsRightContinuousPath.isCadlagPath_comp_of_monotone
    {f : ℝ≥0 → ℝ} (hf : IsRightContinuousPath f) (hmf : Monotone f)
    {q : ℝ≥0 → ℝ≥0} (hq : Continuous q) (hmq : Monotone q) :
    IsCadlagPath (fun t ↦ f (q t)) := by
  refine ⟨?_, fun t _ ↦ ⟨_, (hmf.comp hmq).tendsto_leftLim t⟩⟩
  intro t
  exact (hf (q t)).comp hq.continuousAt.continuousWithinAt (fun _ hst ↦ hmq hst)

end ProbabilityTheory
