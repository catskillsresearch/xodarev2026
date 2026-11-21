/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableLocalization
public import StochLean.Probability.Process.FiniteVariation.MonotoneIntegrable
public import StochLean.Probability.Process.Path.Subtraction

/-! # Locally integrable increasing processes have locally integrable variation

The local integrability assumption uses the original process and Mathlib's
native positive-lifetime masked localization. Each localized row has actual
integrable values at zero and at every deterministic positive integer cap.

After a cap, subtracting that row's initial value gives a zero-initial
increasing process bounded by the integrable difference of its two endpoint
values. The existing monotone-envelope result proves global integrable
variation. Adding back the time-constant initial path changes no need for
an initial moment in the original process. Native localization idempotence
then yields locally integrable variation.

No zero initial value, nonnegativity, initial integrability, jump-supremum
integrability, or additional process or localization owner is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ}

/-- An adapted cadlag increasing process with locally integrable coordinates
has locally integrable variation. The coordinate-localizing sequence retains
its native positive-lifetime mask, including at zero and infinity. -/
theorem HasMonotonePaths.hasLocallyIntegrableVariation_of_locally_integrable
    (hm : HasMonotonePaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P)
    (hL : Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F A P) :
    HasLocallyIntegrableVariation A F P := by
  obtain ⟨τ, hτ, hiτ⟩ := hL
  have hloc : Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F A P := by
    refine ⟨τ, hτ, fun n ↦ ?_⟩
    let E := {ω | 0 < τ n ω}
    let Y := MeasureTheory.stoppedProcess (fun t ↦ E.indicator (A t)) (τ n)
    have hiY (t : ℝ≥0) : Integrable (Y t) P := hiτ n t
    have hE : MeasurableSet[F 0] E := (hτ.isStoppingTime n).measurableSet_gt 0
    have hcMask := hc.indicator E
    have hcY : HasCadlagPaths Y P := hcMask.stoppedProcess (τ n)
    have haY : Adapted F Y :=
      ((ha.indicator_initial hE).stronglyAdapted.stoppedProcess_of_usual hF
        hcMask.hasRightContinuousPaths (hτ.isStoppingTime n)).adapted
    have hmY : HasMonotonePaths Y P := (hm.indicator E).stoppedProcess (τ n)
    let κ (k : ℕ) (_ : Ω) : WithTop ℝ≥0 := (((k + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)
    have hκ : IsLocalizingSequence F κ P := by
      refine ⟨⟨fun k ↦ isStoppingTime_const F ((k + 1 : ℕ) : ℝ≥0), ?_⟩, ?_⟩
      · exact Eventually.of_forall fun _ ↦ WithTop.tendsto_coe_atTop.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).comp (tendsto_add_atTop_nat 1))
      · exact Eventually.of_forall fun _ k l hkl ↦
          WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (Nat.succ_le_succ hkl))
    apply hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    refine ⟨κ, hκ, fun k ↦ ?_⟩
    let T : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0)
    let Z := MeasureTheory.stoppedProcess Y (κ k)
    let I : ℝ≥0 → Ω → ℝ := fun _ ↦ Y 0
    let B := Z - I
    let U : Ω → ℝ := fun ω ↦ Y T ω - Y 0 ω
    have heZ (t : ℝ≥0) (ω : Ω) : Z t ω = Y (min t T) ω := by
      simp only [Z, MeasureTheory.stoppedProcess, κ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe, T]
    have haZ : Adapted F Z :=
      (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
        (hκ.isStoppingTime k)).adapted
    have hcZ : HasCadlagPaths Z P := hcY.stoppedProcess (κ k)
    have haI : Adapted F I := fun _ ↦ (haY 0).mono (F.mono bot_le) le_rfl
    have hcI : HasCadlagPaths I P := Eventually.of_forall fun _ ↦
      IsContinuousPath.isCadlagPath continuous_const
    have haB : Adapted F B := haZ.sub haI
    have hcB : HasCadlagPaths B P := hcZ.sub hcI
    have hmB : HasMonotonePaths B P := by
      filter_upwards [hmY.stoppedProcess (κ k)] with ω hω s t hst
      exact sub_le_sub_right (hω hst) (Y 0 ω)
    have hB0 : B 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ by
      change Z 0 ω - Y 0 ω = 0
      rw [heZ, min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le), sub_self]
    have hiU : Integrable U P := (hiY T).sub (hiY 0)
    have hB : ∀ᵐ ω ∂P, ∀ t, 0 ≤ B t ω ∧ B t ω ≤ U ω := by
      filter_upwards [hmY] with ω hω t
      change 0 ≤ Z t ω - Y 0 ω ∧ Z t ω - Y 0 ω ≤ Y T ω - Y 0 ω
      rw [heZ]
      exact ⟨sub_nonneg.mpr (hω bot_le),
        sub_le_sub_right (hω (min_le_right t T)) _⟩
    have hvB : HasIntegrableVariation B P :=
      (hmB.hasIntegrableVariation_of_integrable_bound haB hF hcB hB0 hiU hB).1
    have he : B + I = Z := sub_add_cancel Z I
    change HasIntegrableVariation Z P
    rw [← he]
    exact hvB.add (hasIntegrableVariation_const (Y 0)) haB haI hF hcB hcI
  exact hasLocallyIntegrableVariation_of_locally hF ha hc hloc

end ProbabilityTheory
