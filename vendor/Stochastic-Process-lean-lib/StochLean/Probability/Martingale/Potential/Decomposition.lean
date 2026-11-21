/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Potential.Basic
public import StochLean.Probability.Martingale.Doob.Supermartingale
public import StochLean.Probability.Martingale.Convergence.MonotoneL1
public import StochLean.ForMathlib.Probability.DoobUniqueness

/-! # Doob decomposition of a discrete potential

Protter III.9, printed pp.106--107 (PDF pp.117--118). The actual increasing
predictable process has an integrable terminal limit. That limit closes the
martingale part, and its mean is the initial potential's mean. Existence uses
only the native discrete Doob parts; uniqueness allows AE normalization and
modification identities and concludes indistinguishability.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem IsPotential.doob_decomposition_closing (hX : IsPotential X F P) :
    let A := predictablePart (-X) F P
    let M := -martingalePart (-X) F P
    ∃ Z : Ω → ℝ, Integrable Z P ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
      (∫ ω, Z ω ∂P) = (∫ ω, X 0 ω ∂P) ∧
      (∀ᵐ ω ∂P, (∀ n, A n ω ≤ Z ω) ∧ Tendsto (fun n ↦ A n ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n ↦ eLpNorm (A n - Z) 1 P) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (M n - Z) 1 P) atTop (𝓝 0) ∧
      (∀ n, M n =ᵐ[P] P[Z | F n]) ∧ UniformIntegrable M 1 P := by
  intro A M
  obtain ⟨hM, hA, hA0, hM0, he, hmA, hnA, hiA, hEA⟩ :=
    hX.supermartingale.doob_decomposition_data
  have hb (n) : (∫ ω, A n ω ∂P) ≤ ∫ ω, X 0 ω ∂P := by
    rw [hEA n]
    exact sub_le_self _ (integral_nonneg_of_ae (hX.nonneg n))
  obtain ⟨Z, hiZ, hlZ, _, hLA⟩ :=
    hmA.exists_integrable_limit_of_nonneg_of_integral_bounded hA.stronglyAdapted.adapted hiA
      (fun n ↦ hnA.mono fun _ hω ↦ hω n) hb
  have hLM : Tendsto (fun n ↦ eLpNorm (M n - Z) 1 P) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n ↦ eLpNorm (X n) 1 P + eLpNorm (A n - Z) 1 P)
        atTop (𝓝 0) := by simpa only [add_zero] using hX.tendsto_eLpNorm.add hLA
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    intro n
    change eLpNorm (M n - Z) 1 P ≤ eLpNorm (X n) 1 P + eLpNorm (A n - Z) 1 P
    have heM : M n - Z = X n + (A n - Z) := by
      funext ω
      have h := congrFun (congrFun he n) ω
      change M n ω - A n ω = X n ω at h
      change M n ω - Z ω = X n ω + (A n ω - Z ω)
      linarith
    rw [heM]
    exact eLpNorm_add_le (hX.supermartingale.integrable n).aestronglyMeasurable
      ((hiA n).sub hiZ).aestronglyMeasurable le_rfl
  have hc := hM.eq_condExp_of_tendsto_eLpNorm hiZ hLM
  have hEZ : (∫ ω, Z ω ∂P) = ∫ ω, X 0 ω ∂P := by
    calc
      _ = ∫ ω, P[Z | F 0] ω ∂P := (integral_condExp (F.le 0)).symm
      _ = ∫ ω, M 0 ω ∂P := integral_congr_ae (hc 0).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun ω ↦ congrFun hM0 ω)
  have hnZ : ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    filter_upwards [hnA, hlZ] with ω ha hz
    exact (ha 0).trans (hz.1 0)
  exact ⟨Z, hiZ, hnZ, hEZ, hlZ, hLA, hLM, hc,
    (hiZ.uniformIntegrable_condExp F.le).ae_eq (fun n ↦ (hc n).symm)⟩

/-- The source decomposition exists and is unique among predictable,
AE-zero-starting decompositions with a true martingale part. -/
theorem IsPotential.exists_unique_doob_decomposition (hX : IsPotential X F P) :
    ∃ (M A : ℕ → Ω → ℝ) (Z : Ω → ℝ),
      Martingale M F P ∧ UniformIntegrable M 1 P ∧ IsStronglyPredictable F A ∧
      A 0 = 0 ∧ M 0 = X 0 ∧ M - A = X ∧ HasMonotonePaths A P ∧
      Integrable Z P ∧ (∫ ω, Z ω ∂P) = (∫ ω, X 0 ω ∂P) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (Z ω))) ∧
      (∀ n, M n =ᵐ[P] P[Z | F n]) ∧
      ∀ N B : ℕ → Ω → ℝ, Martingale N F P → IsStronglyPredictable F B →
        B 0 =ᵐ[P] 0 → IsModification X (N - B) P →
        Indistinguishable M N P ∧ Indistinguishable A B P := by
  obtain ⟨hM, hA, hA0, hM0, he, hmA, _, _, _⟩ :=
    hX.supermartingale.doob_decomposition_data
  obtain ⟨Z, hiZ, _, hEZ, hlZ, _, _, hc, hu⟩ := hX.doob_decomposition_closing
  refine ⟨_, _, Z, hM, hu, hA, hA0, hM0, he, hmA, hiZ, hEZ,
    hlZ.mono fun _ hω ↦ hω.2, hc, fun N B hN hB hB0 hXB ↦ ?_⟩
  apply doob_decomposition_indistinguishable hM hN hA hB
    (Filter.Eventually.of_forall fun ω ↦ congrFun hA0 ω) hB0 _ hXB
  exact fun n ↦ Filter.Eventually.of_forall fun ω ↦ (congrFun (congrFun he n) ω).symm

end ProbabilityTheory
