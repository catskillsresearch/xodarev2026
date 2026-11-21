/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.MomentCriterion

/-! # The extended terminal raw quadratic variation

The terminal bracket is the supremum of the existing raw bracket on integer
times. Its equality to the supremum on the entire half-line and its limit
property hold on one common event. Initial squares are retained. Integrable
terminal energy yields a true finite-time L2 martingale with a uniform second
moment bound; no terminal value of the martingale is assumed or asserted here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Extended terminal energy of the existing raw bracket, including its
initial square. No real conversion or finite-energy assumption is used. -/
noncomputable def IsSemimartingale.quadraticVariationInfinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (hX.quadraticVariation hF (n : ℝ≥0) ω)

theorem IsSemimartingale.measurable_quadraticVariationInfinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Measurable (hX.quadraticVariationInfinity hF) :=
  Measurable.iSup fun n ↦
    ((hX.adapted_quadraticVariation hF (n : ℝ≥0)).mono (F.le _) le_rfl).ennreal_ofReal

/-- One event controls all finite times, not just each time separately. -/
theorem IsSemimartingale.quadraticVariation_le_infinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t, ENNReal.ofReal (hX.quadraticVariation hF t ω) ≤
      hX.quadraticVariationInfinity hF ω := by
  filter_upwards [hX.hasMonotonePaths_quadraticVariation hF] with ω hω t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact (ENNReal.ofReal_le_ofReal (hω hn)).trans (le_iSup
    (fun n : ℕ ↦ ENNReal.ofReal (hX.quadraticVariation hF (n : ℝ≥0) ω)) n)

theorem IsSemimartingale.quadraticVariationInfinity_eq_iSup
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, hX.quadraticVariationInfinity hF ω =
      ⨆ t : ℝ≥0, ENNReal.ofReal (hX.quadraticVariation hF t ω) := by
  filter_upwards [hX.quadraticVariation_le_infinity hF] with ω hω
  apply le_antisymm
  · exact iSup_le fun n ↦ le_iSup
      (fun t : ℝ≥0 ↦ ENNReal.ofReal (hX.quadraticVariation hF t ω)) (n : ℝ≥0)
  · exact iSup_le hω

theorem IsSemimartingale.ae_tendsto_quadraticVariation_infinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ ENNReal.ofReal (hX.quadraticVariation hF t ω))
      atTop (𝓝 (hX.quadraticVariationInfinity hF ω)) := by
  filter_upwards [hX.hasMonotonePaths_quadraticVariation hF,
    hX.quadraticVariationInfinity_eq_iSup hF] with ω hm he
  rw [he]
  exact tendsto_atTop_iSup (fun _ _ h ↦ ENNReal.ofReal_le_ofReal (hm h))

theorem IsSemimartingale.lintegral_quadraticVariationInfinity_eq_iSup
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) =
      ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (hX.quadraticVariation hF (n : ℝ≥0) ω) ∂P := by
  apply lintegral_iSup'
    (fun n ↦ ((hX.adapted_quadraticVariation hF (n : ℝ≥0)).mono
      (F.le _) le_rfl).ennreal_ofReal.aemeasurable)
  filter_upwards [hX.hasMonotonePaths_quadraticVariation hF] with ω hω i j hij
  exact ENNReal.ofReal_le_ofReal (hω (by exact_mod_cast hij))

theorem IsSemimartingale.ae_quadraticVariationInfinity_lt_top
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∀ᵐ ω ∂P, hX.quadraticVariationInfinity hF ω < ∞ :=
  ae_lt_top (hX.measurable_quadraticVariationInfinity hF) hI.ne

theorem IsSemimartingale.integrable_toReal_quadraticVariationInfinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    Integrable (fun ω ↦ (hX.quadraticVariationInfinity hF ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top
    (hX.measurable_quadraticVariationInfinity hF).aemeasurable hI.ne

theorem IsSemimartingale.integrable_quadraticVariation_of_integrable_infinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) (T : ℝ≥0) :
    Integrable (hX.quadraticVariation hF T) P := by
  have hn : 0 ≤ᵐ[P] hX.quadraticVariation hF T :=
    (hX.initial_sq_le_quadraticVariation hF).mono fun ω hω ↦ (sq_nonneg _).trans (hω T)
  apply (lintegral_ofReal_ne_top_iff_integrable
    (((hX.adapted_quadraticVariation hF T).mono (F.le T) le_rfl).aestronglyMeasurable) hn).mp
  exact ((lintegral_mono_ae
    ((hX.quadraticVariation_le_infinity hF).mono fun _ hω ↦ hω T)).trans_lt hI).ne

theorem IsSemimartingale.integral_quadraticVariation_le_integral_infinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) (T : ℝ≥0) :
    (∫ ω, hX.quadraticVariation hF T ω ∂P) ≤
      (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal := by
  rw [← integral_toReal (hX.measurable_quadraticVariationInfinity hF).aemeasurable
    (hX.ae_quadraticVariationInfinity_lt_top hF hI)]
  apply integral_mono_ae (hX.integrable_quadraticVariation_of_integrable_infinity hF hI T)
    (hX.integrable_toReal_quadraticVariationInfinity hF hI)
  filter_upwards [hX.quadraticVariation_le_infinity hF,
    hX.ae_quadraticVariationInfinity_lt_top hF hI] with ω hω hf
  exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).mp (hω T)

variable [SigmaFiniteFiltration P F]

/-- Finite expected terminal raw energy gives true finite-time L2
martingality, not merely L2 at individual times. -/
theorem IsSemimartingale.squareIntegrable_of_integrable_quadraticVariationInfinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    IsSquareIntegrableMartingale X F P :=
  hX.isSquareIntegrableMartingale_of_integrable_quadraticVariation hF hM
    (hX.integrable_quadraticVariation_of_integrable_infinity hF hI)

theorem IsSemimartingale.second_moment_le_integral_quadraticVariationInfinity
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) (T : ℝ≥0) :
    (∫ ω, X T ω ^ 2 ∂P) ≤ (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal := by
  rw [← (hX.integrable_quadraticVariation_and_integral_eq hF
    (hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI) T).2]
  exact hX.integral_quadraticVariation_le_integral_infinity hF hI T

end ProbabilityTheory
