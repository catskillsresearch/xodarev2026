/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.UniformLimit
public import StochLean.Probability.Process.Path.RightLimit

/-! # Locally uniform limits of caglad paths with vanishing right increments

Left continuity passes to locally uniform limits. If the approximating
caglad paths have uniformly vanishing right increments, their actual strict
right-limit paths have the same locally uniform limit. The existing
right-continuous uniform-limit theorem then gives continuity of the limit.

The right-increment bound includes time zero. No approximant is assumed to
equal its right limit at zero, and no continuous limit is supplied as a
certificate. Completeness of the state space is not needed: the relevant
right limits already exist by the caglad hypotheses.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

section Metric

variable {E : Type*} [MetricSpace E] {x : ℕ → ℝ≥0 → E} {y : ℝ≥0 → E}
  {ε : ℕ → ℝ}

theorem isLeftContinuousPath_of_locallyUniform
    (hx : ∀ n, IsLeftContinuousPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T)) : IsLeftContinuousPath y := by
  intro t
  have hq : 𝓝[≤] t ≤ 𝓟 (Icc 0 t) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨bot_le, hs⟩
  exact ((hu t).tendstoUniformlyOnFilter.mono_right hq).tendsto_of_eventually_tendsto
    (Eventually.of_forall fun n ↦ hx n t) ((hu t).tendsto_at ⟨bot_le, le_rfl⟩)

/-- Uniformly small distance to the strict right-limit function preserves
uniform convergence on a set. This is a metric estimate, not a limit selector. -/
theorem tendstoUniformlyOn_rightLim_of_uniform_dist_bound {s : Set ℝ≥0}
    (hu : TendstoUniformlyOn x y atTop s) (hε : Tendsto ε atTop (𝓝 0))
    (hgap : ∀ n t, t ∈ s → dist (Function.rightLim (x n) t) (x n t) ≤ ε n) :
    TendstoUniformlyOn (fun n ↦ Function.rightLim (x n)) y atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (η / 2) (half_pos hη),
    hε.eventually (gt_mem_nhds (half_pos hη))] with n hn hεn
  intro t ht
  have hd : dist (x n t) (Function.rightLim (x n) t) ≤ ε n := by
    simpa only [dist_comm] using hgap n t ht
  calc
    dist (y t) (Function.rightLim (x n) t) ≤
        dist (y t) (x n t) + dist (x n t) (Function.rightLim (x n) t) := dist_triangle _ _ _
    _ < η / 2 + η / 2 := add_lt_add (hn t ht) (hd.trans_lt hεn)
    _ = η := add_halves η

/-- A locally uniform limit is continuous when all actual right increments
of the caglad approximants vanish uniformly, including at the initial time. -/
theorem continuous_of_locallyUniform_caglad_of_rightLim_dist_le
    (hx : ∀ n, IsCagladPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T))
    (hε : Tendsto ε atTop (𝓝 0))
    (hgap : ∀ n t, dist (Function.rightLim (x n) t) (x n t) ≤ ε n) : Continuous y := by
  have hleft : IsLeftContinuousPath y :=
    isLeftContinuousPath_of_locallyUniform (fun n ↦ (hx n).1) hu
  have hur : ∀ T, TendstoUniformlyOn (fun n ↦ Function.rightLim (x n)) y
      atTop (Icc 0 T) := fun T ↦
    tendstoUniformlyOn_rightLim_of_uniform_dist_bound (hu T) hε (fun n t _ ↦ hgap n t)
  have hr : ∀ n, IsRightContinuousPath (Function.rightLim (x n)) := by
    intro n t
    exact continuousWithinAt_rightLim_Ici (tendsto_rightLim_of_tendsto ((hx n).2 t))
  have hright : IsRightContinuousPath y := isRightContinuousPath_of_locallyUniform hr hur
  exact continuous_iff_continuousAt.mpr fun t ↦
    continuousAt_iff_continuous_left_right.mpr ⟨hleft t, hright t⟩

end Metric

section Normed

variable {E : Type*} [NormedAddCommGroup E] {x : ℕ → ℝ≥0 → E} {y : ℝ≥0 → E}
  {ε : ℕ → ℝ}

/-- Norm form of the deterministic continuity bridge. The bound concerns
strict right increments, not the left jumps of a cadlag process. -/
theorem continuous_of_locallyUniform_caglad_of_rightLim_norm_le
    (hx : ∀ n, IsCagladPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T))
    (hε : Tendsto ε atTop (𝓝 0))
    (hgap : ∀ n t, ‖Function.rightLim (x n) t - x n t‖ ≤ ε n) : Continuous y :=
  continuous_of_locallyUniform_caglad_of_rightLim_dist_le hx hu hε
    (fun n t ↦ by simpa only [dist_eq_norm] using hgap n t)

end Normed

end ProbabilityTheory
