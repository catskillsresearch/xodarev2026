/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Martingale
public import StochLean.Probability.Process.Poisson.SecondMoments
public import StochLean.Probability.Process.Semimartingale.CanonicalDecomposition

/-! # Canonical Poisson decomposition and genuine classical nonuniqueness

For an actual Poisson process with future increments independent of the chosen
past, the existing compensated count is a true martingale. The deterministic
linear drift is continuous, predictable, and of finite variation. They give
specialness and identify the existing source canonical parts by uniqueness.

At positive rate the two classical decompositions `(0, N)` and
`(N - rate * time, rate * time)` are genuinely different. The exact second
moment at time one rules out an indistinguishably zero compensated process.
Both normalized reconstructions retain the original time-constant initial
random value; its removal is justified on the common event `N 0 = 0`.

These are parameterized results for a supplied actual Poisson process, not
an assertion of a newly constructed sample-space model. Independence from
the chosen filtration is explicit. No new compensated-process or canonical
component selector is defined.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

private theorem linear_drift_data (rate : ℝ≥0) :
    IsStronglyPredictable F (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) ∧
      HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P ∧
      HasFiniteVariationPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P ∧
      (fun (_ : Ω) ↦ (rate : ℝ) * (0 : ℝ≥0)) = 0 := by
  have ha : Adapted F (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) :=
    fun _ ↦ measurable_const
  have hc : Continuous (fun t : ℝ≥0 ↦ (rate : ℝ) * t) :=
    continuous_const.mul NNReal.continuous_coe
  have hm : Monotone (fun t : ℝ≥0 ↦ (rate : ℝ) * t) :=
    fun _ _ h ↦ mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr h) rate.2
  refine ⟨ha.isStronglyPredictable_of_leftContinuous
    (fun _ _ ↦ hc.continuousAt.continuousWithinAt),
    Eventually.of_forall (fun _ ↦ hc), ?_, ?_⟩
  · exact Eventually.of_forall fun _ ↦ (hm.monotoneOn Set.univ).locallyBoundedVariationOn
  · funext ω
    simp only [NNReal.coe_zero, mul_zero, Pi.zero_apply]

variable [IsProbabilityMeasure P]

/-- The real Poisson count is special, and the sole source canonical parts
are the existing compensated count and deterministic linear drift. -/
theorem IsPoissonProcess.special_decomposition_of_indep_past
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P)
    (hF : F.IsUsual P) :
    ∃ hS : IsSpecialSemimartingale (fun t ω ↦ (N t ω : ℝ)) F P,
      Indistinguishable hS.canonicalMartingalePart
        (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) P ∧
      Indistinguishable hS.canonicalFiniteVariationPart
        (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ)
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t
  let D : ℝ≥0 → Ω → ℝ := fun t _ ↦ (rate : ℝ) * t
  have haX : Adapted F X := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  have hM : IsLocalMartingale M F P := hN.isLocalMartingale_compensated_of_indep_past ha hi
  obtain ⟨hpD, hcD, hvD, hD0⟩ := linear_drift_data (F := F) (P := P) rate
  have hX0 : X 0 =ᵐ[P] 0 := by
    filter_upwards [hN.initial] with ω hω
    change (N 0 ω : ℝ) = 0
    rw [hω, Nat.cast_zero]
  have hM0 : M 0 =ᵐ[P] 0 := by
    simpa only [M, X, NNReal.coe_zero, mul_zero, sub_zero] using hX0
  have hD0ae : D 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ congrFun hD0 ω
  have he : Indistinguishable X ((fun _ ↦ X 0) + M + D) P := by
    filter_upwards [hX0] with ω hω t
    change X t ω = (X 0 ω + (X t ω - D t ω)) + D t ω
    rw [hω, Pi.zero_apply, zero_add, sub_add_cancel]
  have hS : IsSpecialSemimartingale X F P :=
    ⟨haX, hN.hasCadlagPaths_real, M, D, hM, hpD, hcD.hasCadlagPaths,
      hvD, hM0, hD0ae, he⟩
  have heRaw : Indistinguishable X (M + D) P :=
    Eventually.of_forall fun _ _ ↦ (sub_add_cancel _ _).symm
  exact ⟨hS, hS.canonicalDecomposition_unique hF hM hpD hvD hD0ae heRaw⟩

/-- At positive rate, both explicit normalized classical decompositions are
valid and their local-martingale parts are not indistinguishable. The finite-
variation part of a classical decomposition is therefore not unique. -/
theorem IsPoissonProcess.classical_decompositions_nonunique_of_pos
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P)
    (hF : F.IsUsual P) (hrate : 0 < rate) :
    let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ)
    let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t
    let D : ℝ≥0 → Ω → ℝ := fun t _ ↦ (rate : ℝ) * t
    (IsLocalMartingale (0 : ℝ≥0 → Ω → ℝ) F P ∧ Adapted F X ∧
      HasCadlagPaths X P ∧ HasFiniteVariationPaths X P ∧
      (0 : ℝ≥0 → Ω → ℝ) 0 =ᵐ[P] 0 ∧ X 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + 0 + X) P) ∧
    (IsLocalMartingale M F P ∧ Adapted F D ∧ HasCadlagPaths D P ∧
      HasFiniteVariationPaths D P ∧ M 0 =ᵐ[P] 0 ∧ D 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + M + D) P) ∧
    ¬ Indistinguishable (0 : ℝ≥0 → Ω → ℝ) M P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ)
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t
  let D : ℝ≥0 → Ω → ℝ := fun t _ ↦ (rate : ℝ) * t
  have haX : Adapted F X := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  have hM : IsLocalMartingale M F P := hN.isLocalMartingale_compensated_of_indep_past ha hi
  have hZero : IsLocalMartingale (0 : ℝ≥0 → Ω → ℝ) F P := by
    simpa only [sub_self] using hM.sub hM hF
  obtain ⟨hpD, hcD, hvD, hD0⟩ := linear_drift_data (F := F) (P := P) rate
  have hX0 : X 0 =ᵐ[P] 0 := by
    filter_upwards [hN.initial] with ω hω
    change (N 0 ω : ℝ) = 0
    rw [hω, Nat.cast_zero]
  have hM0 : M 0 =ᵐ[P] 0 := by
    simpa only [M, X, NNReal.coe_zero, mul_zero, sub_zero] using hX0
  have heZero : Indistinguishable X ((fun _ ↦ X 0) + 0 + X) P := by
    filter_upwards [hX0] with ω hω t
    change X t ω = (X 0 ω + 0) + X t ω
    rw [hω, Pi.zero_apply, zero_add, zero_add]
  have heComp : Indistinguishable X ((fun _ ↦ X 0) + M + D) P := by
    filter_upwards [hX0] with ω hω t
    change X t ω = (X 0 ω + (X t ω - D t ω)) + D t ω
    rw [hω, Pi.zero_apply, zero_add, sub_add_cancel]
  refine ⟨⟨hZero, haX, hN.hasCadlagPaths_real, hN.hasFiniteVariationPaths_real,
    Eventually.of_forall (fun _ ↦ rfl), hX0, heZero⟩,
    ⟨hM, hpD.stronglyAdapted.adapted, hcD.hasCadlagPaths, hvD, hM0,
      Eventually.of_forall (fun ω ↦ congrFun hD0 ω), heComp⟩, ?_⟩
  intro he
  have heSq : (fun ω ↦ (N 1 ω : ℝ) ^ 2) =ᵐ[P] fun _ ↦ (rate : ℝ) ^ 2 := by
    filter_upwards [he.ae_eq 1] with ω hω
    change 0 = (N 1 ω : ℝ) - (rate : ℝ) * (1 : ℝ≥0) at hω
    simp only [NNReal.coe_one, mul_one] at hω
    rw [sub_eq_zero.mp hω.symm]
  have heInt : (∫ ω, (N 1 ω : ℝ) ^ 2 ∂P) = (rate : ℝ) ^ 2 := by
    calc
      _ = ∫ _ : Ω, (rate : ℝ) ^ 2 ∂P := integral_congr_ae heSq
      _ = _ := by simp
  have hsecond := (hN.hasLaw 1).integral_natCast_sq_poissonMeasure
  rw [heInt] at hsecond
  simp only [mul_one] at hsecond
  have hr : 0 < (rate : ℝ) := by exact_mod_cast hrate
  nlinarith only [hsecond, hr]

end ProbabilityTheory
