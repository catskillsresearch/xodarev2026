/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Extending the time index by its terminal sigma-field

The terminal sigma-field is the supremum of the finite-time filtration,
not the ambient measurable space. This agrees with the existing stopping
sigma-field at the constant infinite stopping time.
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def Filtration.withTerminal (F : Filtration ℝ≥0 mΩ) : Filtration (WithTop ℝ≥0) mΩ :=
  ⟨fun t ↦ WithTop.recTopCoe (⨆ s, F s) (fun s ↦ F s) t, by
    intro i j hij
    cases i using WithTop.recTopCoe with
    | top =>
      have hj : j = ⊤ := top_le_iff.mp hij
      subst j
      exact le_rfl
    | coe i =>
      cases j using WithTop.recTopCoe with
      | top => exact le_iSup (fun s ↦ F s) i
      | coe j => exact F.mono (WithTop.coe_le_coe.mp hij), by
    intro t
    cases t using WithTop.recTopCoe with
    | top => exact iSup_le F.le
    | coe t => exact F.le t⟩

@[simp] theorem Filtration.withTerminal_coe (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    F.withTerminal (t : WithTop ℝ≥0) = F t := rfl

@[simp] theorem Filtration.withTerminal_top (F : Filtration ℝ≥0 mΩ) :
    F.withTerminal ⊤ = ⨆ t, F t := rfl

theorem IsStoppingTime.measurableSpace_top {F : Filtration ℝ≥0 mΩ}
    (hτ : IsStoppingTime F (fun _ ↦ (⊤ : WithTop ℝ≥0))) :
    hτ.measurableSpace = ⨆ t, F t := by
  ext s
  rw [hτ.measurableSet]
  constructor
  · exact fun h ↦ h.1
  · intro hs
    refine ⟨hs, fun i ↦ ?_⟩
    have he : {ω : Ω | (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h ↦ WithTop.coe_ne_top (top_le_iff.mp h)
    rw [he, Set.inter_empty]
    exact @MeasurableSet.empty Ω (F i)

end MeasureTheory
