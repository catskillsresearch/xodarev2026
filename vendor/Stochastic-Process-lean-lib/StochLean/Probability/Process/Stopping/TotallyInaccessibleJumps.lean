/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Classification
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Processes whose positive-time jumps are totally inaccessible

The source hypothesis is countable coverage of the nonzero positive-time jump graph by actual
totally inaccessible stopping times. It does not include adaptedness or path regularity, and it
does not constrain the initial value: the source convention makes `jumpProcess X 0 = X 0`.
Coverage implies zero jumps at predictable stopping times and total inaccessibility of any
stopping time carried by the nonzero positive-time jump graph. All statements use finite graph
points directly; no evaluation at an artificial finite replacement for infinity is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Countably many totally inaccessible stopping times cover every nonzero positive-time jump
on one common full-measure event. Initial values, adaptedness and path regularity are separate
hypotheses rather than part of this jump-coverage predicate. -/
def HasTotallyInaccessibleJumps (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  ∃ σ : ℕ → Ω → WithTop ℝ≥0,
    (∀ n, IsTotallyInaccessibleStoppingTime F (σ n) P) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → jumpProcess X t ω ≠ 0 →
        ∃ n : ℕ, σ n ω = (t : WithTop ℝ≥0)

variable {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Every continuous process satisfies the positive-time jump hypothesis, even with a nonzero
or nonintegrable initial value. The witnessing stopping times are all infinite. -/
theorem HasContinuousPaths.hasTotallyInaccessibleJumps (hX : HasContinuousPaths X P)
    (F : Filtration ℝ≥0 mΩ) : HasTotallyInaccessibleJumps F X P := by
  refine ⟨fun _ _ ↦ ⊤, fun _ ↦ isTotallyInaccessibleStoppingTime_top F P, ?_⟩
  filter_upwards [hX] with ω hω
  intro t ht hj
  exact (hj (hω.jumpProcess_eq_zero (ne_of_gt ht))).elim

/-- The positive jump-coverage condition is invariant under indistinguishability, not merely
under equality almost surely at each separate deterministic time. -/
theorem HasTotallyInaccessibleJumps.congr (hX : HasTotallyInaccessibleJumps F X P)
    (hXY : Indistinguishable X Y P) : HasTotallyInaccessibleJumps F Y P := by
  obtain ⟨σ, hσ, hcover⟩ := hX
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hcover, hXY.jumpProcess] with ω hω he
  intro t ht hj
  apply hω t ht
  simpa only [he t] using hj

/-- A predictable stopping time cannot carry a nonzero positive-time jump of a process with
totally inaccessible jumps. The statement only evaluates genuine finite graph points. -/
theorem HasTotallyInaccessibleJumps.ae_jumpProcess_eq_zero_at_predictable
    (hX : HasTotallyInaccessibleJumps F X P) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsPredictableStoppingTime F ρ P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ρ ω = (t : WithTop ℝ≥0) → jumpProcess X t ω = 0 := by
  obtain ⟨σ, hσ, hcover⟩ := hX
  have hnull (n : ℕ) : ∀ᵐ ω ∂P, ¬ (σ n ω = ρ ω ∧ σ n ω ≠ ⊤) := by
    rw [ae_iff]
    simpa only [not_not] using (hσ n).2 ρ hρ
  filter_upwards [hcover, ae_all_iff.mpr hnull] with ω hω hn
  intro t ht hρt
  by_contra hj
  obtain ⟨n, hnt⟩ := hω t ht hj
  exact hn n ⟨hnt.trans hρt.symm,
    fun htop ↦ WithTop.coe_ne_top (hnt.symm.trans htop)⟩

/-- At each fixed positive deterministic time the jump vanishes almost surely. The exceptional
event may depend on the time; this does not assert absence of random-time jumps. -/
theorem HasTotallyInaccessibleJumps.ae_jumpProcess_eq_zero
    (hX : HasTotallyInaccessibleJumps F X P) {t : ℝ≥0} (ht : 0 < t) :
    jumpProcess X t =ᵐ[P] (fun _ ↦ 0) := by
  have h := hX.ae_jumpProcess_eq_zero_at_predictable (isPredictableStoppingTime_const F P t)
  filter_upwards [h] with ω hω
  exact hω t ht rfl

/-- Any stopping time whose finite graph is carried by the nonzero positive-time jump graph is
totally inaccessible. This is derived from the actual countable covering times, not assumed as
an additional classification principle. -/
theorem HasTotallyInaccessibleJumps.isTotallyInaccessibleStoppingTime_of_jump_graph
    (hX : HasTotallyInaccessibleJumps F X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hgraph : ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      ∃ t : ℝ≥0, 0 < t ∧ τ ω = (t : WithTop ℝ≥0) ∧ jumpProcess X t ω ≠ 0) :
    IsTotallyInaccessibleStoppingTime F τ P := by
  refine ⟨hτ, fun ρ hρ ↦ ?_⟩
  have hzero := hX.ae_jumpProcess_eq_zero_at_predictable hρ
  have hnull : ∀ᵐ ω ∂P, ¬ (τ ω = ρ ω ∧ τ ω ≠ ⊤) := by
    filter_upwards [hgraph, hzero] with ω hω hz
    rintro ⟨he, hf⟩
    obtain ⟨t, ht, hτt, hj⟩ := hω hf
    exact hj (hz t ht (he.symm.trans hτt))
  simpa only [not_not] using ae_iff.mp hnull

/-- In particular, a stopping time selecting positive-time jumps with norm bounded below by
a strictly positive threshold is totally inaccessible. Its infinite samples impose no jump
condition and introduce no artificial terminal value. -/
theorem HasTotallyInaccessibleJumps.isTotallyInaccessibleStoppingTime_of_norm_jump_ge
    (hX : HasTotallyInaccessibleJumps F X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) {b : ℝ} (hb : 0 < b)
    (hgraph : ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      ∃ t : ℝ≥0, 0 < t ∧ τ ω = (t : WithTop ℝ≥0) ∧ b ≤ ‖jumpProcess X t ω‖) :
    IsTotallyInaccessibleStoppingTime F τ P := by
  apply hX.isTotallyInaccessibleStoppingTime_of_jump_graph hτ
  filter_upwards [hgraph] with ω hω hf
  obtain ⟨t, ht, hτt, hbJ⟩ := hω hf
  refine ⟨t, ht, hτt, ?_⟩
  intro hj
  rw [hj, norm_zero] at hbJ
  exact (not_le_of_gt hb) hbJ

end ProbabilityTheory
