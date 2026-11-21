/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Martingale
public import StochLean.Probability.Process.Poisson.Counting
public import StochLean.Probability.Process.Counting.ArrivalJumpGraph
public import StochLean.Probability.Process.LocalMartingale.TotallyInaccessibleJumps

/-! # Actual Poisson jumps and arrivals are totally inaccessible

The original real counting process minus its deterministic rate drift is
the genuine compensated local martingale. Its positive-time jumps are
the count's actual nonnegative unit jumps, since the drift is continuous.
The established predictable-test classification therefore gives the
existing countable totally-inaccessible-jump property.

Every finite original hitting arrival lies on that positive unit-jump
graph, so its native stopping time is totally inaccessible as well.
The rate may be zero, and infinite arrival tails are retained. Independence
of increments from the chosen filtration's past remains an explicit
assumption: no assertion is made for arbitrary enlarged filtrations or
that this independence has already been derived for a natural filtration.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

/-- Under actual independence from the chosen past, the original real
Poisson process has a genuine countable totally inaccessible jump cover. -/
theorem hasTotallyInaccessibleJumps_real_of_indep_past
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P) :
    HasTotallyInaccessibleJumps F (fun t ω ↦ (N t ω : ℝ)) P := by
  have hcount := hN.isNonexplosiveCountingProcess hF ha
  have hcontinuous :
      HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P :=
    ae_of_all _ fun _ ↦ continuous_const.mul NNReal.continuous_coe
  apply hasTotallyInaccessibleJumps_of_localMartingale_sub_continuous
    (hN.isLocalMartingale_compensated_of_indep_past ha hi) hF
    hN.hasCadlagPaths_real hcontinuous
  filter_upwards [hcount.unitJumps] with ω hω t ht
  rcases hω t ht with hj | hj <;> simp only [hj, le_refl, zero_le_one]

/-- Each original Poisson hitting arrival is totally inaccessible, with
no assumption that this arrival is finite and no positive-rate restriction. -/
theorem isTotallyInaccessibleStoppingTime_hittingAfter_of_indep_past
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P) (n : ℕ) :
    IsTotallyInaccessibleStoppingTime F (hittingAfter N (Ioi n) 0) P := by
  have hcount := hN.isNonexplosiveCountingProcess hF ha
  have hTI := hN.hasTotallyInaccessibleJumps_real_of_indep_past hF ha hi
  apply hTI.isTotallyInaccessibleStoppingTime_of_jump_graph
    (hcount.isStoppingTime_hittingAfter ha hF n)
  filter_upwards [hcount.ae_hittingAfter_jump_eq_one] with ω hω hfinite
  obtain ⟨t, ht, hnt, hj⟩ := hω n hfinite
  refine ⟨t, ht, hnt, ?_⟩
  rw [hj]
  exact one_ne_zero

end ProbabilityTheory.IsPoissonProcess
