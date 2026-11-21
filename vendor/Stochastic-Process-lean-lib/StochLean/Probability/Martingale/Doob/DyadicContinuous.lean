/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicUCP
public import StochLean.Probability.Process.UCP.CagladContinuousLimit
public import StochLean.Probability.Process.UCP.MonotoneLimit
public import StochLean.Probability.Process.Path.FiniteVariation

/-! # Constructing the continuous increasing dyadic limit

The actual dyadic steps are UCP-Cauchy. Their right increments are bounded
by the actual global conditional moduli, which tend to zero in probability.
Existing adapted UCP completeness therefore constructs a continuous limit.
Its monotonicity and initial normalization follow from the original steps.
There is no compensator, continuous limit or dyadic convergence certificate input.
The generic interface takes convergence of a genuine conditional modulus; the
original TI source interface constructs that modulus and its convergence internally.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

theorem Supermartingale.exists_continuous_dyadicDoob_limit_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hGM : TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    ∃ A : ℝ≥0 → Ω → ℝ, Adapted F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  let R : ℕ → Ω → ℝ := fun n ω ↦ (G ((1 / 2 : ℝ≥0) ^ n) ω).toReal
  have hR : TendstoInMeasure P R atTop 0 :=
    hGM.comp (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
  have hgap (n : ℕ) : ∀ᵐ ω ∂P, ∀ t,
      ‖rightLimitProcess (dyadicDoobStep X F P n) t ω - dyadicDoobStep X F P n t ω‖ ≤
        R n ω :=
    hX.ae_forall_norm_rightLimitProcess_dyadicDoobStep_sub_le_of_bound n
      (fun t ↦ hbound.mono fun _ hω ↦ hω t) (hG _)
  obtain ⟨B, hBa, hBc, hlim⟩ :=
    CauchyUCP.exists_everywhere_continuous_limit_of_caglad
      (hX.cauchyUCP_dyadicDoobStep_of_globalConditionalModulus hF hc hN hbound hG hG2 hGE)
        (fun n ↦ dyadicDoobStep_adapted X F P n) hF
        (fun n ↦ Eventually.of_forall fun ω ↦ dyadicDoobStep_isCagladPath X F P n ω)
        hR hgap
  have hzero : B 0 =ᵐ[P] (fun _ ↦ 0) := hlim.ae_eq_initial
    (fun n ↦ Eventually.of_forall fun ω ↦ congrFun (dyadicDoobStep_zero X F P n) ω)
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦ B t ω - B 0 ω
  have hAa : Adapted F A := fun t ↦
    (hBa t).sub ((hBa 0).mono (F.mono bot_le) le_rfl)
  have he : Indistinguishable B A P := by
    filter_upwards [hzero] with ω hω t
    simp only [A, hω, sub_zero]
  have hlimA : TendstoUCP P (dyadicDoobStep X F P) atTop A := hlim.congr_right he
  have hmono : HasMonotonePaths A P := hlimA.hasMonotonePaths hX.dyadicDoobStep_monotone
  refine ⟨A, hAa, fun ω ↦ (hBc ω).sub continuous_const, ?_, hmono,
    hmono.hasFiniteVariationPaths, hlimA⟩
  funext ω
  exact sub_self _

/-- The original TI source interface is retained, with its actual modulus constructed internally. -/
theorem Supermartingale.exists_continuous_dyadicDoob_limit
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ A : ℝ≥0 → Ω → ℝ, Adapted F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  obtain ⟨G, hG, hGM, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.exists_continuous_dyadicDoob_limit_of_globalConditionalModulus
    hF hc hN hbound hG hGM hG2 hGE

end MeasureTheory
