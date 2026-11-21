/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.TerminalVariation
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Integrable variation on the whole half-line

The variation owner is Mathlib's `eVariationOn`, not a new terminal process.
Finiteness almost surely is an explicit part of the predicate: integrability
of `toReal` alone would incorrectly accept infinite variation, since that
conversion sends infinity to zero.

Adaptedness, cadlag paths, and the zero initial value in Protter's normalized
FV convention are separate hypotheses. In particular an arbitrary random
process constant in time has zero variation, even without a measurable or
integrable initial value. This module does not define local integrable
variation or choose a terminal limit of the process.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Finite total path variation almost surely, with integrable actual total
variation. No initial-value or process measurability condition is implicit. -/
def HasIntegrableVariation (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  HasFiniteTotalVariationPaths X P ∧
    Integrable (fun ω ↦ (eVariationOn (X · ω) univ).toReal) P

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem HasIntegrableVariation.hasFiniteTotalVariationPaths
    (hX : HasIntegrableVariation X P) : HasFiniteTotalVariationPaths X P := hX.1

theorem HasIntegrableVariation.hasFiniteVariationPaths
    (hX : HasIntegrableVariation X P) : HasFiniteVariationPaths X P :=
  hX.1.hasFiniteVariationPaths

theorem HasIntegrableVariation.integrable_eVariationOn_toReal
    (hX : HasIntegrableVariation X P) :
    Integrable (fun ω ↦ (eVariationOn (X · ω) univ).toReal) P := hX.2

theorem HasIntegrableVariation.ae_eVariationOn_ne_top
    (hX : HasIntegrableVariation X P) :
    ∀ᵐ ω ∂P, eVariationOn (X · ω) univ ≠ ∞ := hX.1

/-- The norm of every increment is bounded on one common path event. -/
theorem HasIntegrableVariation.ae_forall_norm_sub_le
    (hX : HasIntegrableVariation X P) :
    ∀ᵐ ω ∂P, ∀ s t, ‖X t ω - X s ω‖ ≤ (eVariationOn (X · ω) univ).toReal := by
  filter_upwards [hX.1] with ω hω s t
  simpa only [dist_eq_norm] using hω.dist_le (mem_univ t) (mem_univ s)

/-- Compact-horizon variation is bounded by the actual full variation, with
finiteness proved before making the real-valued comparison. -/
theorem HasIntegrableVariation.ae_forall_totalVariationProcess_le
    (hX : HasIntegrableVariation X P) :
    ∀ᵐ ω ∂P, ∀ t,
      totalVariationProcess X t ω ≤ (eVariationOn (X · ω) univ).toReal := by
  filter_upwards [hX.1] with ω hω t
  rw [totalVariationProcess_eq_toReal]
  exact ENNReal.toReal_mono hω (eVariationOn.mono _ (subset_univ (Icc 0 t)))

theorem HasIntegrableVariation.congr (hX : HasIntegrableVariation X P)
    (hXY : Indistinguishable X Y P) : HasIntegrableVariation Y P := by
  constructor
  · filter_upwards [hX.1, hXY] with ω hω hXYω
    simpa only [hXYω] using hω
  · apply hX.2.congr
    filter_upwards [hXY] with ω hω
    simp only [hω]

private theorem eVariationOn_const_path (C : ℝ) :
    eVariationOn (fun _ : ℝ≥0 ↦ C) univ = 0 := by
  apply (eVariationOn.eq_zero_iff _).mpr
  intro s _ t _
  exact edist_self C

/-- The initial random value needs neither measurability nor integrability. -/
theorem hasIntegrableVariation_const (C : Ω → ℝ) :
    HasIntegrableVariation (fun _ ↦ C) P := by
  constructor
  · exact ae_of_all _ fun ω ↦ by
      change eVariationOn (fun _ : ℝ≥0 ↦ C ω) univ ≠ ∞
      rw [eVariationOn_const_path]
      exact ENNReal.zero_ne_top
  · simp only [eVariationOn_const_path, ENNReal.toReal_zero]
    exact ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩

@[simp] theorem hasIntegrableVariation_zero : HasIntegrableVariation (0 : ℝ≥0 → Ω → ℝ) P :=
  hasIntegrableVariation_const 0

/-- Even without process measurability, the definition makes the actual
extended total variation almost everywhere measurable, not merely its real
conversion. -/
theorem HasIntegrableVariation.aemeasurable_eVariationOn
    (hX : HasIntegrableVariation X P) :
    AEMeasurable (fun ω ↦ eVariationOn (X · ω) univ) P := by
  apply hX.2.aemeasurable.ennreal_ofReal.congr
  filter_upwards [hX.1] with ω hω
  exact ENNReal.ofReal_toReal hω

theorem HasIntegrableVariation.lintegral_eVariationOn_lt_top
    (hX : HasIntegrableVariation X P) :
    (∫⁻ ω, eVariationOn (X · ω) univ ∂P) < ∞ :=
  lt_top_iff_ne_top.mpr
    ((integrable_toReal_iff hX.aemeasurable_eVariationOn hX.ae_eVariationOn_ne_top).mp hX.2)

/-- The finite extended-integral characterization includes actual AE
measurability; no finiteness is hidden by `toReal`. -/
theorem hasIntegrableVariation_iff_aemeasurable_lintegral_lt_top :
    HasIntegrableVariation X P ↔
      AEMeasurable (fun ω ↦ eVariationOn (X · ω) univ) P ∧
        (∫⁻ ω, eVariationOn (X · ω) univ ∂P) < ∞ := by
  constructor
  · intro hX
    exact ⟨hX.aemeasurable_eVariationOn, hX.lintegral_eVariationOn_lt_top⟩
  · rintro ⟨hm, hi⟩
    exact ⟨(ae_lt_top' hm hi.ne).mono fun _ hω ↦ hω.ne,
      integrable_toReal_of_lintegral_ne_top hm hi.ne⟩

theorem hasIntegrableVariation_iff_lintegral_lt_top
    (hm : AEMeasurable (fun ω ↦ eVariationOn (X · ω) univ) P) :
    HasIntegrableVariation X P ↔ (∫⁻ ω, eVariationOn (X · ω) univ ∂P) < ∞ := by
  rw [hasIntegrableVariation_iff_aemeasurable_lintegral_lt_top, and_iff_right hm]

/-- Adaptedness and usual cadlag paths supply exact measurability of the
original extended variation; they are not fields of the predicate. -/
theorem hasIntegrableVariation_iff_lintegral_lt_top_of_usual
    {F : Filtration ℝ≥0 mΩ} (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    HasIntegrableVariation X P ↔ (∫⁻ ω, eVariationOn (X · ω) univ ∂P) < ∞ :=
  hasIntegrableVariation_iff_lintegral_lt_top
    (ha.measurable_eVariationOn_univ_of_usual hF hc).aemeasurable

end ProbabilityTheory
