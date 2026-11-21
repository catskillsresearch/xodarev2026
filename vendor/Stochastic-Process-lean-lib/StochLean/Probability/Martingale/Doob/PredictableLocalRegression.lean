/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableLocal
public import StochLean.Probability.Martingale.MonotonePaths

/-! # A genuinely non-Class-D local Doob decomposition

On any usual probability filtration, the deterministic process `X t = -t`
is a continuous supermartingale, but is not Class D. We apply the actual
general local decomposition theorem first, and only then use predictable
finite-variation uniqueness to identify its constructed compensator with
`t` and its local martingale with zero.

The resulting compensator has locally integrable variation, not integrable
variation on the whole half-line. The latter obstruction uses the common
pathwise increment bound of actual finite total variation, so no conversion
of infinite extended variation to the real number zero is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

/-- Deterministic-time L1 norms alone already preclude Class D for `X t = -t`. -/
theorem not_isClassD_negative_time :
    ¬ IsClassD (fun (t : ℝ≥0) (_ : Ω) ↦ -(t : ℝ)) F P := by
  intro hD
  obtain ⟨C, hC⟩ := hD.uniformIntegrable.2.2
  have he := hC (C + 1)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (hD.integrable (C + 1))] at he
  have hn : (∫ _ : Ω, ‖-((C + 1 : ℝ≥0) : ℝ)‖ ∂P) ≤ (C : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp
    simpa only [ENNReal.ofReal_coe_nnreal] using he
  rw [norm_neg, Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hn
  have hbad : (C : ℝ) + 1 ≤ (C : ℝ) := by
    simpa only [integral_const, probReal_univ, one_smul,
      NNReal.coe_add, NNReal.coe_one] using hn
  linarith

/-- Linear deterministic growth cannot have finite total variation on the
whole half-line, hence cannot have integrable variation there. -/
theorem not_hasIntegrableVariation_time :
    ¬ HasIntegrableVariation (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P := by
  intro hv
  obtain ⟨ω, hω⟩ := hv.ae_forall_norm_sub_le.exists
  let V := (eVariationOn (fun t : ℝ≥0 ↦ (t : ℝ)) univ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let t : ℝ≥0 := ⟨V + 1, by positivity⟩
  have hbad := hω 0 t
  change ‖(V + 1) - 0‖ ≤ V at hbad
  rw [sub_zero, Real.norm_of_nonneg (by positivity : 0 ≤ V + 1)] at hbad
  linarith

/-- The actual general local theorem constructs a decomposition outside
Class D. Predictable FV uniqueness then identifies its part with `t`, so
the compensated local martingale is zero and global IV is genuinely absent. -/
theorem exists_predictable_local_decomposition_negative_time (hF : F.IsUsual P) :
    let X : ℝ≥0 → Ω → ℝ := fun t _ ↦ -(t : ℝ)
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (X + A) F P ∧
      Indistinguishable A (fun t _ ↦ (t : ℝ)) P ∧
      Indistinguishable (X + A) 0 P ∧ ¬ HasIntegrableVariation A P := by
  let X : ℝ≥0 → Ω → ℝ := fun t _ ↦ -(t : ℝ)
  let C : ℝ≥0 → Ω → ℝ := fun t _ ↦ (t : ℝ)
  have haC : Adapted F C := fun _ ↦ measurable_const
  have hmC : HasMonotonePaths C P := Eventually.of_forall fun _ _ _ hst ↦ hst
  have hcontC (ω : Ω) : IsContinuousPath (C · ω) := NNReal.continuous_coe
  have hcontX (ω : Ω) : IsContinuousPath (X · ω) := (hcontC ω).neg
  have hcX : HasCadlagPaths X P := Eventually.of_forall fun ω ↦
    (hcontX ω).isCadlagPath
  have hX : Supermartingale X F P :=
    (hmC.submartingale haC (fun _ ↦ integrable_const _)).neg
  obtain ⟨A, hpA, hcA, h0A, hmA, hvA, hMA, _⟩ :=
    hX.exists_predictable_doob_local_decomposition hF hcX
  have hpC : IsStronglyPredictable F C :=
    haC.isStronglyPredictable_of_leftContinuous fun ω ↦
      (hcontC ω).isLeftContinuousPath
  have hXC : X + C = 0 := by
    funext t ω
    exact neg_add_cancel (t : ℝ)
  have hMC : IsLocalMartingale (X + C) F P := by
    rw [hXC]
    exact (martingale_zero ℝ F P).isLocalMartingale
      (Eventually.of_forall fun _ ↦ IsContinuousPath.isCadlagPath continuous_const)
  have h0 : A 0 =ᵐ[P] C 0 := Eventually.of_forall fun ω ↦ congrFun h0A ω
  have hAC : Indistinguishable A C P :=
    indistinguishable_of_predictable_finiteVariation_localMartingale_add hF hMA hMC
      hpA hpC hvA.hasFiniteVariationPaths hmC.hasFiniteVariationPaths h0
  refine ⟨A, hpA, hcA, h0A, hmA, hvA, hMA, hAC, ?_, ?_⟩
  · filter_upwards [hAC] with ω hω t
    change -(t : ℝ) + A t ω = 0
    rw [hω t]
    exact neg_add_cancel (t : ℝ)
  · intro hv
    exact not_hasIntegrableVariation_time (hv.congr hAC)

end ProbabilityTheory
