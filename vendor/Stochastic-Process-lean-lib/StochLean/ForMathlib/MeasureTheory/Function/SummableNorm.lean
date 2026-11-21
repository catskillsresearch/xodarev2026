/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # A genuinely summable integrable norm envelope

Summable first absolute moments imply almost-sure pointwise norm summability,
integrability of the actual real norm series, and the corresponding integral
identity. Tonelli first proves finiteness of the extended nonnegative series;
only afterwards is its real conversion used. Neither a finite measure nor
pointwise summability on exceptional samples is assumed.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {f : ℕ → Ω → E}

/-- Summable integrals of norms produce one common event of absolute
summability and an actual integrable norm-sum envelope with its exact mean. -/
theorem ae_summable_norm_and_integrable_tsum_norm (hi : ∀ n, Integrable (f n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖f n ω‖ ∂P)) :
    (∀ᵐ ω ∂P, Summable (fun n ↦ ‖f n ω‖)) ∧
      Integrable (fun ω ↦ ∑' n, ‖f n ω‖) P ∧
      (∫ ω, ∑' n, ‖f n ω‖ ∂P) = ∑' n, ∫ ω, ‖f n ω‖ ∂P := by
  let G : Ω → ℝ≥0∞ := fun ω ↦ ∑' n, ENNReal.ofReal ‖f n ω‖
  have hm : AEMeasurable G P :=
    AEMeasurable.tsum (fun n ↦ (hi n).norm.aemeasurable.ennreal_ofReal)
  have hG : (∫⁻ ω, G ω ∂P) = ENNReal.ofReal (∑' n, ∫ ω, ‖f n ω‖ ∂P) := by
    calc
      _ = ∑' n, ∫⁻ ω, ENNReal.ofReal ‖f n ω‖ ∂P :=
        lintegral_tsum (fun n ↦ (hi n).norm.aemeasurable.ennreal_ofReal)
      _ = ∑' n, ENNReal.ofReal (∫ ω, ‖f n ω‖ ∂P) := by
        apply tsum_congr
        intro n
        simpa only [ofReal_norm, enorm_eq_nnnorm, coe_nnnorm] using
          lintegral_coe_eq_integral (fun ω ↦ ‖f n ω‖₊) (hi n).norm
      _ = ENNReal.ofReal (∑' n, ∫ ω, ‖f n ω‖ ∂P) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n ↦ integral_nonneg fun ω ↦ norm_nonneg (f n ω)) hs).symm
  have hGfin : (∫⁻ ω, G ω ∂P) ≠ ∞ := by
    rw [hG]
    exact ENNReal.ofReal_ne_top
  have hf : ∀ᵐ ω ∂P, G ω ≠ ∞ := (ae_lt_top' hm hGfin).mono fun _ hω ↦ hω.ne
  have hpoint : ∀ᵐ ω ∂P, Summable (fun n ↦ ‖f n ω‖) := by
    filter_upwards [hf] with ω hω
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    simpa only [G, ofReal_norm] using hω
  have he (ω : Ω) : (G ω).toReal = ∑' n, ‖f n ω‖ := by
    change (∑' n, ENNReal.ofReal ‖f n ω‖).toReal = _
    rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)]
  refine ⟨hpoint, ?_, ?_⟩
  · exact (integrable_toReal_of_lintegral_ne_top hm hGfin).congr
      (Eventually.of_forall he)
  · exact (integral_tsum_of_summable_integral_norm (fun n ↦ (hi n).norm)
      (by simpa only [norm_norm] using hs)).symm

end MeasureTheory
