/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Caglad
public import Mathlib.Topology.Order.LeftRightLim
public import StochLean.ForMathlib.Topology.Order.LeftLimitRight

/-! # Source left limits and jumps

The Protter convention is `X_(0-) = 0`, not `X_0`. At positive times the
canonical Mathlib strict-left limit is reused; all mathematical limit identities
are proved on the cadlag domain. No limit property is asserted for an arbitrary
path on which a left limit does not exist.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def leftLimitProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 then 0 else Function.leftLim (fun s ↦ X s ω) t

noncomputable def jumpProcess (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  X - leftLimitProcess X

@[simp] theorem leftLimitProcess_zero (X : ℝ≥0 → Ω → ℝ) : leftLimitProcess X 0 = 0 := by
  funext ω
  simp [leftLimitProcess]

@[simp] theorem jumpProcess_zero (X : ℝ≥0 → Ω → ℝ) : jumpProcess X 0 = X 0 := by
  simp [jumpProcess]

theorem IsCadlagPath.tendsto_leftLimitProcess {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsCadlagPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    Tendsto (fun s ↦ X s ω) (𝓝[<] t) (𝓝 (leftLimitProcess X t ω)) := by
  simp only [leftLimitProcess, if_neg ht]
  exact tendsto_leftLim_of_tendsto (h.2 t ht)

theorem IsContinuousPath.leftLimitProcess_eq {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsContinuousPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    leftLimitProcess X t ω = X t ω := by
  simp only [leftLimitProcess, if_neg ht]
  exact h.continuousWithinAt.leftLim_eq

theorem IsContinuousPath.jumpProcess_eq_zero {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsContinuousPath (fun t ↦ X t ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    jumpProcess X t ω = 0 := by
  change X t ω - leftLimitProcess X t ω = 0
  rw [h.leftLimitProcess_eq ht, sub_self]

theorem IsCadlagPath.isCagladPath_leftLimitProcess {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsCadlagPath (fun t ↦ X t ω)) :
    IsCagladPath (fun t ↦ leftLimitProcess X t ω) := by
  constructor
  · intro t
    by_cases ht : t = 0
    · subst t
      simpa only [show Set.Iic (0 : ℝ≥0) = {0} from Set.Iic_bot] using
        (continuousWithinAt_singleton (f := fun s ↦ leftLimitProcess X s ω) (x := 0))
    · have heq : (fun s ↦ Function.leftLim (fun u ↦ X u ω) s) =ᶠ[𝓝 t]
          fun s ↦ leftLimitProcess X s ω := by
        filter_upwards [Ioi_mem_nhds (pos_iff_ne_zero.mpr ht)] with s hs
        have hs' : 0 < s := hs
        simp only [leftLimitProcess, if_neg (ne_of_gt hs')]
      have hl := continuousWithinAt_leftLim_Iic (tendsto_leftLim_of_tendsto (h.2 t ht))
      exact hl.congr_of_eventuallyEq
        (heq.symm.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds.symm
  · intro t
    refine ⟨X t ω, ?_⟩
    apply (h.1 t).tendsto_leftLim_nhdsGT.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hp : 0 < s := lt_of_le_of_lt bot_le hs
    simp only [leftLimitProcess, if_neg (ne_of_gt hp)]

theorem HasCadlagPaths.hasCagladPaths_leftLimitProcess {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : HasCadlagPaths X P) : HasCagladPaths (leftLimitProcess X) P :=
  h.mono fun _ hω ↦ hω.isCagladPath_leftLimitProcess

theorem Indistinguishable.leftLimitProcess {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (leftLimitProcess X) (leftLimitProcess Y) P := by
  filter_upwards [h] with ω hω
  intro t
  simp only [ProbabilityTheory.leftLimitProcess, hω]

theorem Indistinguishable.jumpProcess {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (jumpProcess X) (jumpProcess Y) P := by
  filter_upwards [h, h.leftLimitProcess] with ω hω hl
  intro t
  change X t ω - ProbabilityTheory.leftLimitProcess X t ω =
    Y t ω - ProbabilityTheory.leftLimitProcess Y t ω
  rw [hω, hl]

end ProbabilityTheory
