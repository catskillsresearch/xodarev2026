/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableRegularization
public import StochLean.Probability.Martingale.Doob.RegularContinuousClassD
public import StochLean.Probability.Process.FiniteVariation.MonotoneIntegrable
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra

/-! # General Class D Doob--Meyer existence

The actual predictable jump-mean correction makes the centered original
Class D supermartingale regular. Its already proved continuous Doob theorem
then supplies the remaining increasing part. Their sum is predictable,
cadlag, increasing and of integrable whole-half-line variation. The original
initial random value is restored to the true uniformly integrable martingale.

This is the general Class D existence direction of Protter III.11, without
value or jump bounds, total inaccessibility, regularity, zero original initial
value, or a proposed decomposition. The predictable increasing part starts
exactly at zero. Its actual integrable terminal and full-time L1 convergence
are constructed from the existing integrable-variation terminal owner.
Uniqueness of supplied predictable FV parts is proved separately and reused
by later localization; no new compensator selector is introduced here.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Every cadlag Class D supermartingale has an actual predictable increasing
integrable-variation compensating part and a true UI martingale. There is no
normalization assumption on X; its initial value remains in the martingale. -/
theorem Supermartingale.exists_predictable_doob_of_classD
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasIntegrableVariation A P ∧ IsClassD A F P ∧
      IsUIMartingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let Y := X - I
  have hI : Martingale I F P :=
    martingale_const_fun F P (hX.stronglyAdapted 0) (hX.integrable 0)
  have hID : IsClassD I F P := isClassD_const (hX.integrable 0)
  have hcI : HasCadlagPaths I P :=
    (show HasContinuousPaths I P from Eventually.of_forall fun _ ↦ continuous_const).hasCadlagPaths
  have hY : Supermartingale Y F P := hX.sub_martingale hI
  have hYD : IsClassD Y F P := hXD.sub hID
  have hcY : HasCadlagPaths Y P := hc.sub hcI
  obtain ⟨C, hpC, hcC, hC0, hmC, hvC, hCD, hYC, hYCD, hcYC, hreg⟩ :=
    hY.exists_predictable_jump_mean_correction hYD hF hcY
  have hYC0 : (Y + C) 0 =ᵐ[P] 0 := by
    filter_upwards with ω
    change X 0 ω - X 0 ω + C 0 ω = 0
    simp only [hC0, Pi.zero_apply, sub_self, add_zero]
  obtain ⟨B, W, haB, hpB, hcB, hB0, hmB, _, _, hMB, _, _, hiW, hW, _, _⟩ :=
    hYC.exists_continuous_doob_of_classD_of_predictable_jump_mean_zero hYCD hF hcYC
      (fun γ hγ hpos ↦ (hreg γ hγ hpos).2) hYC0
  have hcadB : HasCadlagPaths B P :=
    (show HasContinuousPaths B P from Eventually.of_forall hcB).hasCadlagPaths
  have hvB : HasIntegrableVariation B P :=
    (hmB.hasIntegrableVariation_of_integrable_bound haB hF hcadB
      (Eventually.of_forall fun ω ↦ congrFun hB0 ω) hiW hW).1
  let A := C + B
  have hpA : IsStronglyPredictable F A := hpC.add hpB
  have hcA : HasCadlagPaths A P := hcC.add hcadB
  have hA0 : A 0 = 0 := by
    change C 0 + B 0 = 0
    rw [hC0, hB0, add_zero]
  have hmA : HasMonotonePaths A P := by
    filter_upwards [hmC, hmB] with ω hC hB s t hst
    exact add_le_add (hC hst) (hB hst)
  have hvA : HasIntegrableVariation A P :=
    hvC.add hvB hpC.stronglyAdapted.adapted haB hF hcC hcadB
  have hAD : IsClassD A F P :=
    hvA.isClassD hpA.stronglyAdapted.adapted hF hcA (by rw [hA0]; exact integrable_zero _ _ _)
  have hMA : Martingale (X + A) F P := by
    have he : ((Y + C) + B) + I = X + A := by
      funext t ω
      change ((X t ω - X 0 ω + C t ω) + B t ω) + X 0 ω =
        X t ω + (C t ω + B t ω)
      ring
    rw [← he]
    exact hMB.add hI
  obtain ⟨Z, hiZ, hlZ, hL1Z, _, _, _⟩ :=
    hvA.exists_integrable_terminal hpA.stronglyAdapted.adapted hF hcA
      (by rw [hA0]; exact integrable_zero _ _ _)
  refine ⟨A, Z, hpA, hcA, hA0, hmA, hvA, hAD,
    ⟨hMA, (hXD.add hAD).uniformIntegrable⟩, hc.add hcA, hiZ, ?_, hlZ, hL1Z⟩
  filter_upwards [hmA, hlZ] with ω hmω hlω t
  constructor
  · simpa only [hA0, Pi.zero_apply] using hmω (show (0 : ℝ≥0) ≤ t from bot_le)
  · exact ge_of_tendsto hlω ((eventually_ge_atTop t).mono fun u hu ↦ hmω hu)

end MeasureTheory
