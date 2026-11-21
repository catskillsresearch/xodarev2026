/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ClosedRegion
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Right inverses of continuous increasing clocks, including flat intervals

The inverse is the canonical extended first hitting time of a strict upper
level. Its finite value is evaluated only under an actual unboundedness
hypothesis. Continuous unbounded clocks are proper quotient maps, so a
continuous path constant on clock fibers descends continuously. In particular
the inverse itself need not be continuous or a two-sided inverse.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

noncomputable def rightClockInverse (a : ℝ≥0 → ℝ≥0) (s : ℝ≥0) : WithTop ℝ≥0 :=
  hittingAfter (fun t (_ : Unit) ↦ a t) (Ioi s) 0 ()

theorem rightClockInverse_ne_top {a : ℝ≥0 → ℝ≥0} {s : ℝ≥0}
    (hu : ∃ t, s < a t) : rightClockInverse a s ≠ ⊤ := by
  obtain ⟨t, ht⟩ := hu
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (hittingAfter_le_of_mem bot_le ht)

theorem rightClockInverse_mono (a : ℝ≥0 → ℝ≥0) : Monotone (rightClockInverse a) := by
  intro s t hst
  exact hittingAfter_anti (fun t (_ : Unit) ↦ a t) 0 (Ioi_subset_Ioi hst) ()

theorem le_rightClockInverse_iff {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) (s t : ℝ≥0) :
    (t : WithTop ℝ≥0) ≤ rightClockInverse a s ↔ a t ≤ s := by
  constructor
  · intro ht
    have h := mem_of_le_hittingAfter_compl_of_continuous
      (X := fun t (_ : Unit) ↦ a t) (ω := ()) (t := t) hc isClosed_Iic
      (show a 0 ∈ Iic s by change a 0 ≤ s; rw [h0]; exact bot_le)
    exact h (by rw [compl_Iic]; exact ht)
  · intro ht
    apply le_of_not_gt
    intro h
    obtain ⟨u, hu, hau⟩ := hittingAfter_lt_iff.mp h
    exact (not_lt_of_ge ((hm hu.2.le).trans ht)) hau

theorem rightClockInverse_lt_iff {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) (s t : ℝ≥0) :
    rightClockInverse a s < t ↔ s < a t := by
  simpa only [not_le] using not_congr (le_rightClockInverse_iff hc hm h0 s t)

theorem clock_rightClockInverse {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) {s : ℝ≥0}
    (hu : ∃ t, s < a t) : a (rightClockInverse a s).untopA = s := by
  have hn := rightClockInverse_ne_top hu
  have ht : ((rightClockInverse a s).untopA : WithTop ℝ≥0) = rightClockInverse a s := by
    rw [WithTop.untopA_eq_untop hn, WithTop.coe_untop]
  apply le_antisymm ((le_rightClockInverse_iff hc hm h0 _ _).mp ht.le)
  have h := hittingAfter_mem_closure_of_rightContinuous
    (X := fun t (_ : Unit) ↦ a t) (ω := ()) (s := Ioi s)
    (fun _ ↦ hc.continuousWithinAt) hn
  rw [closure_Ioi] at h
  exact h

/-- Exact inverse values can be certified by the whole sublevel set. No
strict increase or separate inverse-existence premise is required. -/
theorem rightClockInverse_eq_iff_sublevel {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) (s T : ℝ≥0) :
    rightClockInverse a s = T ↔ ∀ t, a t ≤ s ↔ t ≤ T := by
  constructor
  · intro h t
    rw [← le_rightClockInverse_iff hc hm h0 s t, h]
    exact WithTop.coe_le_coe
  · intro h
    apply le_antisymm
    · apply WithTop.le_of_forall_lt_iff_le.mp
      intro t ht
      apply le_of_lt
      apply (rightClockInverse_lt_iff hc hm h0 s t).mpr
      exact lt_of_not_ge (fun hle ↦ (not_le_of_gt (WithTop.coe_lt_coe.mp ht)) ((h t).mp hle))
    · exact (le_rightClockInverse_iff hc hm h0 s T).mpr ((h T).mpr le_rfl)

theorem self_le_rightClockInverse_apply {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) (t : ℝ≥0) :
    (t : WithTop ℝ≥0) ≤ rightClockInverse a (a t) :=
  (le_rightClockInverse_iff hc hm h0 _ _).mpr le_rfl

theorem eqOn_clock_Icc_rightClockInverse {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0) (t : ℝ≥0)
    (hu : ∃ u, a t < a u) :
    EqOn a (fun _ ↦ a t) (Icc t (rightClockInverse a (a t)).untopA) := by
  intro u hu'
  exact le_antisymm ((hm hu'.2).trans_eq (clock_rightClockInverse hc hm h0 hu)) (hm hu'.1)

theorem isProperMap_of_continuous_clock {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (hu : ∀ s, ∃ t, s < a t) : IsProperMap a := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hc, fun K hK ↦ ?_⟩
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨T, hT⟩ := hu b
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).of_isClosed_subset (hK.isClosed.preimage hc)
  intro t ht
  refine ⟨bot_le, ?_⟩
  by_contra h
  exact (not_lt_of_ge (hb ht)) (hT.trans_le (hm (le_of_not_ge h)))

theorem isQuotientMap_of_continuous_clock {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0)
    (hu : ∀ s, ∃ t, s < a t) : IsQuotientMap a :=
  (isProperMap_of_continuous_clock hc hm hu).isClosedMap.isQuotientMap hc
    (fun s ↦ ⟨(rightClockInverse a s).untopA, clock_rightClockInverse hc hm h0 (hu s)⟩)

theorem comp_rightClockInverse_clock {E : Type*} {x : ℝ≥0 → E} {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0)
    (hu : ∀ s, ∃ t, s < a t) (hf : ∀ s t, a s = a t → x s = x t) (t : ℝ≥0) :
    x (rightClockInverse a (a t)).untopA = x t :=
  hf _ _ (clock_rightClockInverse hc hm h0 (hu (a t)))

theorem continuous_comp_rightClockInverse {E : Type*} [TopologicalSpace E]
    {x : ℝ≥0 → E} {a : ℝ≥0 → ℝ≥0}
    (hc : Continuous a) (hm : Monotone a) (h0 : a 0 = 0)
    (hu : ∀ s, ∃ t, s < a t) (hx : Continuous x)
    (hf : ∀ s t, a s = a t → x s = x t) :
    Continuous (fun s ↦ x (rightClockInverse a s).untopA) := by
  apply (isQuotientMap_of_continuous_clock hc hm h0 hu).continuous_iff.mpr
  convert hx using 1
  funext t
  exact comp_rightClockInverse_clock hc hm h0 hu hf t

end ProbabilityTheory
