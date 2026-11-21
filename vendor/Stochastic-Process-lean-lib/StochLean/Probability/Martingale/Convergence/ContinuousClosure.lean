/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Reindex
public import StochLean.Probability.Process.LocalMartingale
public import Mathlib.Probability.Martingale.Convergence

/-!
# Closing a continuous-time uniformly integrable martingale

An integer-time restriction supplies an actual integrable terminal variable.
The tower property then closes every real-time coordinate. This implication
requires no path regularity; the almost-sure limit over the entire half-line
is a separate assertion, not confused with convergence along the integers.

Source: the closed/UI equivalence in Protter I.13 (martingale part).
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

/-- A UI martingale has an integrable closing variable, constructed by discrete convergence. -/
theorem exists_integrable_closing (hX : Martingale X F P) (hu : UniformIntegrable X 1 P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∀ t, X t =ᵐ[P] P[Z | F t] := by
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hm : Martingale (fun n ↦ X (e n)) G P := hX.reindex e he
  have hui := hu.reindex e
  let Z := G.limitProcess (fun n ↦ X (e n)) P
  obtain ⟨C, hC⟩ := hui.2.2
  have hi : Integrable Z P := (hm.submartingale.memLp_limitProcess hC).integrable le_rfl
  refine ⟨Z, hi, fun t ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hmZ : X (e n) =ᵐ[P] P[Z | F (e n)] := hm.ae_eq_condExp_limitProcess hui n
  exact (hX.condExp_ae_eq hn).symm.trans ((condExp_congr_ae hmZ).trans
    (condExp_condExp_of_le (F.mono hn) (F.le (e n))))

theorem uniformIntegrable_of_integrable_closing {Z : Ω → ℝ}
    (hi : Integrable Z P) (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) :
    UniformIntegrable X 1 P :=
  (hi.uniformIntegrable_condExp F.le).ae_eq (fun t ↦ (hclose t).symm)

theorem uniformIntegrable_iff_exists_integrable_closing (hX : Martingale X F P) :
    UniformIntegrable X 1 P ↔ ∃ Z : Ω → ℝ, Integrable Z P ∧ ∀ t, X t =ᵐ[P] P[Z | F t] :=
  ⟨hX.exists_integrable_closing, fun ⟨_, hi, hc⟩ ↦ uniformIntegrable_of_integrable_closing hi hc⟩

end MeasureTheory.Martingale
