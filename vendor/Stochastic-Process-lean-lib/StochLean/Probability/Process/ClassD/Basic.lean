/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Finite
public import StochLean.Probability.Process.Equivalence
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Class D: uniform integrability of finite stopping values

The sole Class D predicate concerns the family of all everywhere-finite stopping
times, using the existing `FiniteStoppingTime` witness. Adaptation, cadlag paths,
one-sided martingality and initial normalization are separate hypotheses.
In particular this is not uniform integrability at deterministic times.
Source: Protter III.3, printed p.107 (PDF p.118).
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → E}

/-- Uniform integrability over all finite stopping times, not just constant ones. -/
def IsClassD (X : ℝ≥0 → Ω → E) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  UniformIntegrable (fun τ : FiniteStoppingTime F ↦ fun ω ↦ X (τ ω) ω) 1 P

namespace IsClassD

theorem uniformIntegrable_finiteStoppingTime {ι : Type*} (hX : IsClassD X F P)
    (τ : ι → FiniteStoppingTime F) :
    UniformIntegrable (fun i ω ↦ X (τ i ω) ω) 1 P := hX.reindex τ

theorem uniformIntegrable (hX : IsClassD X F P) : UniformIntegrable X 1 P :=
  hX.uniformIntegrable_finiteStoppingTime (FiniteStoppingTime.const F)

theorem integrable_finiteStoppingTime_value (hX : IsClassD X F P)
    (τ : FiniteStoppingTime F) : Integrable (fun ω ↦ X (τ ω) ω) P :=
  memLp_one_iff_integrable.mp (hX.memLp τ)

theorem integrable (hX : IsClassD X F P) (t : ℝ≥0) : Integrable (X t) P :=
  hX.integrable_finiteStoppingTime_value (FiniteStoppingTime.const F t)

theorem congr (hX : IsClassD X F P) (hXY : Indistinguishable X Y P) : IsClassD Y F P :=
  hX.ae_eq (fun τ ↦ hXY.mono fun ω hω ↦ hω (τ ω))

theorem add (hX : IsClassD X F P) (hY : IsClassD Y F P) : IsClassD (X + Y) F P :=
  UniformIntegrable.add hX hY le_rfl

theorem neg (hX : IsClassD X F P) : IsClassD (-X) F P :=
  hX.mono_norm (fun τ ↦ (hX.1 τ).neg)
    (fun _ ↦ Eventually.of_forall fun _ ↦ (norm_neg _).le)

theorem sub (hX : IsClassD X F P) (hY : IsClassD Y F P) : IsClassD (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

/-- Stopping at a possibly infinite time still samples the original process
at finite times when testing Class D. No terminal value is introduced. -/
theorem stoppedProcess (hX : IsClassD X F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : IsClassD (stoppedProcess X τ) F P := by
  let σ : FiniteStoppingTime F → FiniteStoppingTime F := fun ρ ↦
    FiniteStoppingTime.ofNotTop (ρ.isStoppingTime.min hτ)
      (fun ω ↦ ne_top_of_le_ne_top (ρ.withTop_ne_top ω) (min_le_left _ _))
  exact hX.uniformIntegrable_finiteStoppingTime σ

end IsClassD

theorem isClassD_const {V : Ω → E} (hV : Integrable V P) :
    IsClassD (fun _ : ℝ≥0 ↦ V) F P :=
  uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hV)

theorem isClassD_const_iff {V : Ω → E} :
    IsClassD (fun _ : ℝ≥0 ↦ V) F P ↔ Integrable V P :=
  ⟨fun h ↦ h.integrable 0, isClassD_const⟩

theorem isClassD_iff_of_indistinguishable (hXY : Indistinguishable X Y P) :
    IsClassD X F P ↔ IsClassD Y F P :=
  ⟨fun h ↦ h.congr hXY, fun h ↦ h.congr hXY.symm⟩

end ProbabilityTheory
