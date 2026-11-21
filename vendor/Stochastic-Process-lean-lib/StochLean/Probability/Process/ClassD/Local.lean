/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Basic

/-! # Class DL: a separate UI family on each finite horizon

Class DL and Class D are distinct: the local UI estimate may depend on the
deterministic horizon. Equivalently every deterministic stopped process is
Class D. Adaptation and path regularity are not bundled into either predicate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- UI over stopping times bounded by each prescribed finite horizon. -/
def IsClassDL (X : ℝ≥0 → Ω → E) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  ∀ T : ℝ≥0, UniformIntegrable
    (fun τ : {τ : FiniteStoppingTime F | ∀ ω, τ ω ≤ T} ↦ fun ω ↦ X (τ.1 ω) ω) 1 P

theorem IsClassD.isClassDL (hX : IsClassD X F P) : IsClassDL X F P :=
  fun _ ↦ hX.uniformIntegrable_finiteStoppingTime Subtype.val

theorem IsClassDL.congr {Y : ℝ≥0 → Ω → E} (hX : IsClassDL X F P)
    (hXY : Indistinguishable X Y P) : IsClassDL Y F P :=
  fun T ↦ (hX T).ae_eq (fun τ ↦ hXY.mono fun ω hω ↦ hω (τ.1 ω))

theorem IsClassDL.uniformIntegrable_finiteStoppingTime {ι : Type*}
    (hX : IsClassDL X F P) (τ : ι → FiniteStoppingTime F) {T : ℝ≥0}
    (hb : ∀ i ω, τ i ω ≤ T) : UniformIntegrable (fun i ω ↦ X (τ i ω) ω) 1 P :=
  (hX T).reindex (fun i ↦ ⟨τ i, hb i⟩)

theorem IsClassDL.isClassD_stoppedProcess (hX : IsClassDL X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) : IsClassD (stoppedProcess X τ) F P := by
  let σ : FiniteStoppingTime F → FiniteStoppingTime F := fun ρ ↦
    FiniteStoppingTime.ofNotTop (ρ.isStoppingTime.min hτ)
      (fun ω ↦ ne_top_of_le_ne_top (ρ.withTop_ne_top ω) (min_le_left _ _))
  exact hX.uniformIntegrable_finiteStoppingTime σ
    (fun _ ω ↦ WithTop.untopA_le ((min_le_right _ _).trans (hb ω)))

theorem isClassDL_iff_forall_isClassD_stoppedProcess : IsClassDL X F P ↔
    ∀ T : ℝ≥0, IsClassD (stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0))) F P := by
  constructor
  · exact fun h T ↦ h.isClassD_stoppedProcess (isStoppingTime_const F T) (fun _ ↦ le_rfl)
  · intro h T
    have hu := (h T).uniformIntegrable_finiteStoppingTime
      (fun τ : {τ : FiniteStoppingTime F | ∀ ω, τ ω ≤ T} ↦ τ.1)
    apply hu.ae_eq
    intro τ
    exact Eventually.of_forall fun ω ↦ by
      simp only [stoppedProcess, ← WithTop.coe_min, min_eq_left (τ.2 ω)]
      rfl

end ProbabilityTheory
