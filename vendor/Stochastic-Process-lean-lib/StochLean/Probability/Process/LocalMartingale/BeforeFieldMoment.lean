/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.BeforeSigmaOrder
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Local moments at a time with trivial preceding information

If the sigma-field strictly before a positive deterministic time has only
probability-zero or probability-one events, native local coordinate `MemLp`
already implies `MemLp` of the original coordinate at that time.

The proof finds one actual localizer which is almost surely at least that
time. Thus the positive-lifetime mask is almost surely one; it is not silently
discarded. No adaptedness, path regularity or initial moment is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  {p : ℝ≥0∞} {T : ℝ≥0}

/-- Before-field zero-one information prevents native localization from
removing a moment obstruction at a positive deterministic time. -/
theorem Locally.memLp_at_of_before_zero_one
    (hX : Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, MemLp (Y t) p P) F X P)
    (hT : 0 < T)
    (hzeroOne : ∀ s : Set Ω,
      MeasurableSet[(isStoppingTime_const F T).measurableSpaceBefore] s →
        P s = 0 ∨ P s = 1) :
    MemLp (X T) p P := by
  classical
  obtain ⟨τ, hτ, hLp⟩ := hX
  let E : ℕ → Set Ω := fun n ↦ {ω | (T : WithTop ℝ≥0) ≤ τ n ω}
  have hmE (n : ℕ) :
      MeasurableSet[(isStoppingTime_const F T).measurableSpaceBefore] (E n) := by
    simpa only [E, compl_ofPred, not_lt] using
      ((hτ.isStoppingTime n).measurableSet_lt_before (isStoppingTime_const F T)).compl
  have hex : ∃ n, P (E n) = 1 := by
    by_contra h
    have hz (n : ℕ) : P (E n) = 0 :=
      (hzeroOne (E n) (hmE n)).resolve_right (fun hn ↦ h ⟨n, hn⟩)
    have hnone : ∀ᵐ ω ∂P, ∀ n, ω ∉ E n := by
      refine ae_all_iff.mpr fun n ↦ ?_
      rw [ae_iff]
      simpa only [E, mem_ofPred_eq, not_not] using hz n
    obtain ⟨ω, hω, hlim⟩ := (hnone.and hτ.tendsto_top).exists
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))).exists
    exact hω n hn.le
  obtain ⟨n, hn⟩ := hex
  have hm : MeasurableSet (E n) :=
    (isStoppingTime_const F T).measurableSpaceBefore_le_ambient _ (hmE n)
  have hmem : ∀ᵐ ω ∂P, ω ∈ E n := (mem_ae_iff_prob_eq_one hm).mpr hn
  apply (memLp_congr_ae (g := X T) ?_).mp (hLp n T)
  filter_upwards [hmem] with ω hω
  have hle : (T : WithTop ℝ≥0) ≤ τ n ω := hω
  have hpos : (⊥ : WithTop ℝ≥0) < τ n ω :=
    (WithTop.coe_lt_coe.mpr hT).trans_le hle
  rw [stoppedProcess_eq_of_le hle,
    indicator_of_mem (show ω ∈ {ω | ⊥ < τ n ω} from hpos)]

end ProbabilityTheory
