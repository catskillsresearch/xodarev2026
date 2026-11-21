/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConstancyExit
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalInterval
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Protter II.27, Corollary 5: all constancy intervals on one event

Only a countable dense family of actual departure stopping times is needed.
The existing ordered-stopping equivalence transfers constancy in both
directions; continuity then includes every real endpoint simultaneously.
There are no initial moments or extra bracket owners. The discontinuous
Poisson example is a separate source obligation.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.ae_eqOn_Icc_iff_quadraticVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (EqOn (X · ω) (fun _ ↦ X s ω) (Icc s t) ↔
        EqOn ((hX.isSemimartingale hF).quadraticVariation hF · ω)
          (fun _ ↦ (hX.isSemimartingale hF).quadraticVariation hF s ω) (Icc s t)) := by
  let Q := (hX.isSemimartingale hF).quadraticVariation hF
  have haQ : Adapted F Q := (hX.isSemimartingale hF).adapted_quadraticVariation hF
  have hcQ : HasContinuousPaths Q P := hX.hasContinuousPaths_quadraticVariation hF
  have htransfer (Y : ℝ≥0 → Ω → ℝ) (ha : Adapted F Y) (hc : HasContinuousPaths Y P)
      (r : ℝ≥0) :
      Indistinguishable (MeasureTheory.stoppedProcess X (constancyExit Y r))
          (MeasureTheory.stoppedProcess X (fun _ ↦ r)) P ↔
        Indistinguishable (MeasureTheory.stoppedProcess Q (constancyExit Y r))
          (MeasureTheory.stoppedProcess Q (fun _ ↦ r)) P :=
    (hX.quadraticVariation_stopped_eq_iff hF (isStoppingTime_const F r)
      (ha.isStoppingTime_constancyExit hF hc r)
      (Eventually.of_forall (le_constancyExit Y r))).symm
  have hQstop (n : ℕ) : Indistinguishable
      (MeasureTheory.stoppedProcess Q (constancyExit X (denseSeq ℝ≥0 n)))
      (MeasureTheory.stoppedProcess Q (fun _ ↦ denseSeq ℝ≥0 n)) P :=
    (htransfer X hX.1.1 hX.2 _).mp (hX.2.mono fun _ hω ↦
      stoppedProcess_constancyExit_of_continuous hω _)
  have hXstop (n : ℕ) : Indistinguishable
      (MeasureTheory.stoppedProcess X (constancyExit Q (denseSeq ℝ≥0 n)))
      (MeasureTheory.stoppedProcess X (fun _ ↦ denseSeq ℝ≥0 n)) P :=
    (htransfer Q haQ hcQ _).mpr (hcQ.mono fun _ hω ↦
      stoppedProcess_constancyExit_of_continuous hω _)
  filter_upwards [hX.2, hcQ, ae_all_iff.mpr hQstop, ae_all_iff.mpr hXstop]
    with ω hx hq hQω hXω s t hst
  exact ⟨eqOn_Icc_of_stopped_constancyExit hq hQω hst,
    eqOn_Icc_of_stopped_constancyExit hx hXω hst⟩

/-- On the same common event, equality of the increasing bracket at the
two endpoints exactly detects constancy of the whole process interval. -/
theorem IsContinuousLocalMartingale.ae_quadraticVariation_eq_iff_eqOn_Icc
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      ((hX.isSemimartingale hF).quadraticVariation hF s ω =
          (hX.isSemimartingale hF).quadraticVariation hF t ω ↔
        EqOn (X · ω) (fun _ ↦ X s ω) (Icc s t)) := by
  filter_upwards [hX.ae_eqOn_Icc_iff_quadraticVariation hF,
    (hX.isSemimartingale hF).hasMonotonePaths_quadraticVariation hF] with ω he hm s t hst
  rw [he s t hst]
  constructor
  · intro h u hu
    exact le_antisymm ((hm hu.2).trans_eq h.symm) (hm hu.1)
  · intro h
    exact (h ⟨hst, le_rfl⟩).symm

theorem IsContinuousLocalMartingale.ae_continuousQuadraticVariation_eq_iff_eqOn_Icc
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      ((hX.isSemimartingale hF).continuousQuadraticVariation hF s ω =
          (hX.isSemimartingale hF).continuousQuadraticVariation hF t ω ↔
        EqOn (X · ω) (fun _ ↦ X s ω) (Icc s t)) := by
  filter_upwards [hX.ae_quadraticVariation_eq_iff_eqOn_Icc hF,
    (hX.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous hF hX.2]
    with ω he hq s t hst
  rw [hq s, hq t, sub_left_inj]
  exact he s t hst

/-- Source-facing interval statement: empty, singleton, open, half-open and
unbounded intervals are all included, on one event independent of the interval. -/
theorem IsContinuousLocalMartingale.ae_same_constancy_intervals
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ I : Set ℝ≥0, I.OrdConnected →
      ((∀ s ∈ I, ∀ t ∈ I, X s ω = X t ω) ↔
        (∀ s ∈ I, ∀ t ∈ I, (hX.isSemimartingale hF).quadraticVariation hF s ω =
          (hX.isSemimartingale hF).quadraticVariation hF t ω)) := by
  filter_upwards [hX.ae_eqOn_Icc_iff_quadraticVariation hF] with ω he I hI
  have htrans {f g : ℝ≥0 → ℝ}
      (hfg : ∀ s t, s ≤ t → EqOn f (fun _ ↦ f s) (Icc s t) →
        EqOn g (fun _ ↦ g s) (Icc s t))
      (hf : ∀ s ∈ I, ∀ t ∈ I, f s = f t) : ∀ s ∈ I, ∀ t ∈ I, g s = g t := by
    have hpair (s t : ℝ≥0) (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) : g s = g t := by
      have h := hfg s t hst (fun u hu ↦ hf u (hI.out hs ht hu) s hs)
      exact (h ⟨hst, le_rfl⟩).symm
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hpair s t hs ht hst
    · exact (hpair t s ht hs hts).symm
  exact ⟨htrans (fun s t hst ↦ (he s t hst).mp),
    htrans (fun s t hst ↦ (he s t hst).mpr)⟩

end ProbabilityTheory
