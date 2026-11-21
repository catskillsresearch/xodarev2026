/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import StochLean.Probability.Martingale.Doob.ConditionalModulusConvergence
public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilyVersions
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # Version invariance and almost-sure cadlag input for conditional moduli

Coordinatewise modifications preserve conditional increment moduli. In contrast, the
positive-jump condition is transported only by indistinguishability. Usual completeness
constructs an everywhere-cadlag indistinguishable process before using jump enumeration.

Coherent increment representatives have a measurable literal supremum. These constructions
claim ambient measurability, not automatic preservation of each conditioning sigma-field.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {T δ : ℝ≥0} {W : Ω → ℝ≥0∞}

theorem IsConditionalIncrementModulus.congr_process
    (hW : IsConditionalIncrementModulus F P X T δ W)
    (he : ∀ t : ℝ≥0, X t =ᵐ[P] Y t) : IsConditionalIncrementModulus F P Y T δ W := by
  apply hW.congr_family
  intro i
  exact (condExp_congr_ae ((he i.1.1).sub (he i.1.2))).mono fun _ hω ↦
    congrArg ENNReal.ofReal hω

theorem IsGlobalConditionalIncrementModulus.congr_process
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    (he : ∀ t : ℝ≥0, X t =ᵐ[P] Y t) : IsGlobalConditionalIncrementModulus F P Y δ W := by
  apply hW.congr_family
  intro i
  exact (condExp_congr_ae ((he i.1.1).sub (he i.1.2))).mono fun _ hω ↦
    congrArg ENNReal.ofReal hω

theorem exists_coherent_conditionalIncrementModulus
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [SFinite P]
    (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0) :
    ∃ g : ConditionalIncrementIndex T δ → Ω → ℝ≥0∞,
      (∀ i, Measurable (g i)) ∧
        (∀ i, g i =ᵐ[P] conditionalIncrementFamily F P X T δ i) ∧
          IsConditionalIncrementModulus F P X T δ (fun ω ↦ ⨆ i, g i ω) := by
  obtain ⟨g, hm, he, _, hsup⟩ := exists_measurable_iSup_ae_versions P
    (fun i : ConditionalIncrementIndex T δ ↦
      measurable_conditionalIncrementFamily (F := F) (P := P) (X := X) i)
  exact ⟨g, hm, he, hsup⟩

theorem exists_coherent_globalConditionalIncrementModulus
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [SFinite P]
    (X : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0) :
    ∃ g : GlobalConditionalIncrementIndex δ → Ω → ℝ≥0∞,
      (∀ i, Measurable (g i)) ∧
        (∀ i, g i =ᵐ[P] globalConditionalIncrementFamily F P X δ i) ∧
          IsGlobalConditionalIncrementModulus F P X δ (fun ω ↦ ⨆ i, g i ω) := by
  obtain ⟨g, hm, he, _, hsup⟩ := exists_measurable_iSup_ae_versions P
    (fun i : GlobalConditionalIncrementIndex δ ↦
      measurable_globalConditionalIncrementFamily (F := F) (P := P) (X := X) i)
  exact ⟨g, hm, he, hsup⟩

theorem HasTotallyInaccessibleJumps.tendstoInMeasure_conditionalModulus_of_hasCadlagPaths
    [IsFiniteMeasure P] (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P)
    (hX : Adapted F X) (hc : HasCadlagPaths X P) {N : ℝ} (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ)) :
    TendstoInMeasure P (fun δ ω ↦ (W δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) := by
  obtain ⟨Y, he, hp, hcY⟩ := hX.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hbY : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ N := by
    filter_upwards [he, hbound] with ω heω hbω t
    rw [← heω t]
    exact hbω t
  have hWY (δ : ℝ≥0) : IsConditionalIncrementModulus F P Y T δ (W δ) :=
    (hW δ).congr_process (fun t ↦ he.mono fun _ hω ↦ hω t)
  exact (hJ.congr he).tendstoInMeasure_conditionalModulus hF hp.stronglyAdapted.adapted
    hcY hN hbY hWY

theorem HasTotallyInaccessibleJumps.conditionalModulus_L2_convergence_of_hasCadlagPaths
    [IsFiniteMeasure P] (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P)
    (hX : Adapted F X) (hc : HasCadlagPaths X P) {N : ℝ} (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ)) :
    (∀ δ, MemLp (fun ω ↦ (W δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (W δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
        Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (W δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  obtain ⟨Y, he, hp, hcY⟩ := hX.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hbY : ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ N := by
    filter_upwards [he, hbound] with ω heω hbω t
    rw [← heω t]
    exact hbω t
  have hWY (δ : ℝ≥0) : IsConditionalIncrementModulus F P Y T δ (W δ) :=
    (hW δ).congr_process (fun t ↦ he.mono fun _ hω ↦ hω t)
  exact (hJ.congr he).conditionalModulus_L2_convergence hF hp.stronglyAdapted.adapted
    hcY hN hbY hWY

end ProbabilityTheory
