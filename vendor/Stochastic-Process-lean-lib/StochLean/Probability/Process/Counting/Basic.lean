/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.FiniteVariation
public import StochLean.Probability.Process.Path.LeftLimit
public import Mathlib.Probability.Process.Adapted

/-! # Nonexplosive counting processes

The source process remains a function with natural-number values at every
finite time. This predicate describes the nonexplosive, zero-initial,
unit-jump counting domain; it is deliberately narrower than counting
processes allowed to take an infinite value after an explosion.

Path assumptions hold on common almost-sure events. Adaptedness, a
filtration, independence, and moment assumptions are not part of the
definition. Real cadlag paths and finite variation follow from monotonicity
and right continuity. Jumps use the existing real `jumpProcess`, whose
initial value is the original initial value; the unit-jump field concerns
only positive times.

This file does not construct arrival times or establish the two-way
correspondence with a nonexplosive arrival sequence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace MeasureTheory

/-- Real casting preserves adaptedness of a natural-valued process. No
counting-process or probability-law assumption is needed. -/
theorem Adapted.natCast_real {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {F : Filtration ι mΩ} {N : ι → Ω → ℕ} (ha : Adapted F N) :
    Adapted F (fun t ω ↦ (N t ω : ℝ)) := fun t ↦
  (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A finite-valued, nonexplosive counting process, without a chosen
filtration or a prescribed law. Unit jumps and all path properties are
asserted on common almost-sure events. -/
structure IsNonexplosiveCountingProcess (N : ℝ≥0 → Ω → ℕ)
    (P : Measure Ω := by volume_tac) : Prop where
  aemeasurable : ∀ t, AEMeasurable (N t) P
  initial : N 0 =ᵐ[P] 0
  monotonePaths : HasMonotonePaths N P
  rightContinuousPaths : HasRightContinuousPaths N P
  unitJumps : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
    jumpProcess (fun s v ↦ (N s v : ℝ)) t ω = 0 ∨
      jumpProcess (fun s v ↦ (N s v : ℝ)) t ω = 1

namespace IsNonexplosiveCountingProcess

variable {N : ℝ≥0 → Ω → ℕ} {P : Measure Ω}

/-- Each real-valued count is almost-everywhere measurable. -/
theorem aemeasurable_real (hN : IsNonexplosiveCountingProcess N P) (t : ℝ≥0) :
    AEMeasurable (fun ω ↦ (N t ω : ℝ)) P := by
  have hc : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable
  exact hc.comp_aemeasurable (hN.aemeasurable t)

/-- The real process retains the zero initial count. -/
theorem initial_real (hN : IsNonexplosiveCountingProcess N P) :
    (fun ω ↦ (N 0 ω : ℝ)) =ᵐ[P] 0 := by
  filter_upwards [hN.initial] with ω hω
  change N 0 ω = 0 at hω
  change (N 0 ω : ℝ) = 0
  rw [hω, Nat.cast_zero]

/-- Monotonicity is preserved by the real cast on the same path event. -/
theorem hasMonotonePaths_real (hN : IsNonexplosiveCountingProcess N P) :
    HasMonotonePaths (fun t ω ↦ (N t ω : ℝ)) P := by
  filter_upwards [hN.monotonePaths] with ω hω s t hst
  change (N s ω : ℝ) ≤ (N t ω : ℝ)
  exact_mod_cast hω hst

/-- Real left limits follow from monotonicity; a separate cadlag
assumption is not required in the counting-process definition. -/
theorem hasCadlagPaths_real (hN : IsNonexplosiveCountingProcess N P) :
    HasCadlagPaths (fun t ω ↦ (N t ω : ℝ)) P := by
  filter_upwards [hN.hasMonotonePaths_real, hN.rightContinuousPaths] with ω hmω hrω
  refine ⟨fun t ↦ ?_, fun t _ ↦
    ⟨Function.leftLim (fun s ↦ (N s ω : ℝ)) t, hmω.tendsto_leftLim t⟩⟩
  have hcast : Continuous (fun n : ℕ ↦ (n : ℝ)) := continuous_of_discreteTopology
  exact hcast.continuousAt.comp_continuousWithinAt (hrω t)

/-- Counts have finite variation on every compact time interval. This
does not assert finite total variation on the whole half-line. -/
theorem hasFiniteVariationPaths_real (hN : IsNonexplosiveCountingProcess N P) :
    HasFiniteVariationPaths (fun t ω ↦ (N t ω : ℝ)) P :=
  hN.hasMonotonePaths_real.hasFiniteVariationPaths

/-- The actual positive-time jump norms are at most one on one common
path event. No initial-value convention is silently added to this bound. -/
theorem ae_norm_jumpProcess_real_le_one (hN : IsNonexplosiveCountingProcess N P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess (fun s v ↦ (N s v : ℝ)) t ω‖ ≤ 1 := by
  filter_upwards [hN.unitJumps] with ω hω t ht
  rcases hω t ht with h | h <;> simp only [h, norm_zero, norm_one, zero_le_one, le_refl]

end IsNonexplosiveCountingProcess

end ProbabilityTheory
