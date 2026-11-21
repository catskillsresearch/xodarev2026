/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Probability.Yan
public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.FiniteHorizon
public import StochLean.Probability.Process.Semimartingale.ClassicalLocalization

/-! # The Bichteler--Dellacherie theorem

The good-integrator definition is equivalent to the existence of a classical
local-martingale plus finite-variation decomposition.  On each deterministic
horizon, boundedness in probability of the unit elementary-integral image is
transferred to an equivalent integrability law.  Yan separation produces a
second equivalent law with a uniform expectation bound, Rao supplies a
special decomposition, and Girsanov--Meyer transfers it back.  The independently
chosen finite-horizon decompositions are then aligned and patched globally.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The difficult direction of Bichteler--Dellacherie: a process satisfying
the native good-integrator definition has a classical semimartingale
decomposition. -/
theorem IsSemimartingale.isClassicalSemimartingale
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsClassicalSemimartingale X F P := by
  let _ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  apply isClassicalSemimartingale_of_deterministic_stoppedProcess (hF := hF)
  intro n
  let T : ℝ≥0 := (n + 1 : ℕ)
  let Y : ℝ≥0 → Ω → ℝ := deterministicStoppedProcess X T
  have hstop : MeasureTheory.stoppedProcess X (fun _ ↦ (T : WithTop ℝ≥0)) = Y := by
    funext t ω
    simp only [MeasureTheory.stoppedProcess, Y, deterministicStoppedProcess,
      ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  have htotal : IsTotalSemimartingale Y F P := by
    rw [← hstop]
    exact hX T
  have hBIP_P : IsBoundedInProbability (unitElementaryIntegralSet Y F) P :=
    htotal.2.2.isBoundedInProbability_unitElementaryIntegralSet
  let J : EquivalentIntegrabilityMeasure X T P :=
    Classical.choice (exists_equivalentIntegrabilityMeasure hX.adapted hX.hasCadlagPaths T)
  let _ : IsProbabilityMeasure J.measure := J.isProbabilityMeasure
  obtain ⟨D₀, hD₀, hJP⟩ := J.dominated
  have hBIP_J : IsBoundedInProbability (unitElementaryIntegralSet Y F) J.measure :=
    hBIP_P.mono_measure_of_le_smul hJP hD₀
  let β : Set (Ω → ℝ) := integrableUnitElementaryIntegralSet Y F J.measure
  have hβBIP : IsBoundedInProbability β J.measure :=
    hBIP_J.integrableUnitElementaryIntegralSet
  obtain ⟨R, D, C, hRJ, hJR, hdom, hbound⟩ := yan
    (convex_integrableUnitElementaryIntegralSet (X := Y) (F := F) (Q := J.measure))
    (zero_mem_integrableUnitElementaryIntegralSet (X := Y) (F := F) (Q := J.measure))
    (fun f hf ↦ hf.2) hβBIP
  have hclassY : IsClassicalSemimartingale Y F P := by
    apply J.isClassicalSemimartingale_deterministicStoppedProcess
      hX.adapted hX.hasCadlagPaths hRJ hJR
      (D := (D : ℝ≥0∞)) ENNReal.coe_ne_top (C := C)
    · simpa only [Measure.coe_nnreal_smul] using hdom
    · intro Z hZ
      exact (hbound Z (by simpa only [Y, β] using hZ)).2
    · exact hF
  rw [← hstop] at hclassY
  change IsClassicalSemimartingale
    (MeasureTheory.stoppedProcess X
      (fun _ : Ω ↦ ((((n + 1 : ℕ) : ℝ≥0)) : WithTop ℝ≥0))) F P
  simpa only [T] using hclassY

/-- Bichteler--Dellacherie in iff form, with both directions stated in the
project's native process predicates. -/
theorem isSemimartingale_iff_isClassicalSemimartingale (hF : F.IsUsual P) :
    IsSemimartingale X F P ↔ IsClassicalSemimartingale X F P :=
  ⟨fun hX ↦ hX.isClassicalSemimartingale hF,
    fun hX ↦ hX.isSemimartingale hF⟩

end ProbabilityTheory
