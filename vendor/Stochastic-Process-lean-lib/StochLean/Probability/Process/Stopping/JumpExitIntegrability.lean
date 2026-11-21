/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.JumpCoefficients
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization
public import StochLean.Probability.Process.Measurability.CadlagVersion
public import StochLean.Probability.Process.ClassD.Basic

/-! # Actual jump coefficients at capped norm exits

Usual completeness transfers stopped-field measurability from an everywhere
cadlag indistinguishable version to the original stopped jump coefficient.
The original function is not replaced or redefined on exceptional paths.

At the existing capped norm exits, the left limit is bounded by the exit
level. Class D supplies integrability of the original finite stopping value,
so the actual jump is integrable without bounded jumps or a zero initial
value. Sampling uses `stoppedValueWithTerminal` with explicit terminal zero;
the capped exits are everywhere finite, so this terminal case never occurs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The original zero-terminal stopped jump, not only a modification of it,
is strongly measurable at the native stopped sigma-algebra under usual
conditions and almost-sure cadlag regularity. -/
theorem Adapted.stronglyMeasurable_stopped_jump_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace]
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) := by
  obtain ⟨Y, heq, hY, hcY⟩ := ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hmY := hY.stronglyAdapted.adapted.stronglyMeasurable_stopped_jump hcY hτ
  have hcomplete : IsCompleteSubMeasurableSpace P hτ.measurableSpace := fun s hs ↦
    hτ.le_measurableSpace_of_const_le (fun _ ↦ bot_le) s (hF.complete_initial s hs)
  exact (hcomplete.measurable_congr_ae hmY.measurable
    (heq.jumpProcess.stoppedValueWithTerminal (EventuallyEq.refl _ _) τ).symm).stronglyMeasurable

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Class D and the actual pre-exit left-limit bound control the actual jump
coefficient at every capped norm exit. No jump bound or initial normalization
is assumed, including when an exit occurs at time zero. -/
theorem IsClassD.integrable_and_bound_stopped_jump_cappedNormExitSequence
    (hD : IsClassD X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (n : ℕ) :
    Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (cappedNormExitSequence X n)) P ∧
      ∀ᵐ ω ∂P,
        ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
          (cappedNormExitSequence X n) ω‖ ≤ ((n + 1 : ℕ) : ℝ) +
            ‖stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) (cappedNormExitSequence X n) ω‖ := by
  have hτ := ha.isStoppingTime_cappedNormExitSequence hF hc n
  let σ : FiniteStoppingTime F :=
    FiniteStoppingTime.ofNotTop hτ (cappedNormExitSequence_ne_top X n)
  have hiσ : Integrable (fun ω ↦ X (σ ω) ω) P :=
    hD.integrable_finiteStoppingTime_value σ
  have he : stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) (cappedNormExitSequence X n) =
      fun ω ↦ X (σ ω) ω := by
    funext ω
    rw [stoppedValueWithTerminal_of_ne_top (cappedNormExitSequence_ne_top X n ω)]
    rfl
  have hiX : Integrable
      (stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) (cappedNormExitSequence X n)) P := by
    rw [he]
    exact hiσ
  have hbound : ∀ᵐ ω ∂P,
      ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (cappedNormExitSequence X n) ω‖ ≤ ((n + 1 : ℕ) : ℝ) +
          ‖stoppedValueWithTerminal X (fun _ ↦ (0 : ℝ)) (cappedNormExitSequence X n) ω‖ := by
    filter_upwards [hc] with ω hcω
    rw [stoppedValueWithTerminal_of_ne_top (cappedNormExitSequence_ne_top X n ω),
      stoppedValueWithTerminal_of_ne_top (cappedNormExitSequence_ne_top X n ω)]
    change ‖jumpProcess X (cappedNormExitSequence X n ω).untopA ω‖ ≤
      ((n + 1 : ℕ) : ℝ) + ‖X (cappedNormExitSequence X n ω).untopA ω‖
    have ht : ((cappedNormExitSequence X n ω).untopA : WithTop ℝ≥0) =
        cappedNormExitSequence X n ω := by
      rw [WithTop.untopA_eq_untop (cappedNormExitSequence_ne_top X n ω), WithTop.coe_untop]
    have hl := hcω.norm_leftLimitProcess_le_of_le_cappedNormExitSequence ht.le
    calc
      _ ≤ ‖X (cappedNormExitSequence X n ω).untopA ω‖ +
          ‖leftLimitProcess X (cappedNormExitSequence X n ω).untopA ω‖ := norm_sub_le _ _
      _ ≤ ‖X (cappedNormExitSequence X n ω).untopA ω‖ + ((n + 1 : ℕ) : ℝ) :=
        add_le_add le_rfl hl
      _ = _ := add_comm _ _
  refine ⟨?_, hbound⟩
  apply ((integrable_const (((n + 1 : ℕ) : ℝ))).add hiX.norm).mono' _ hbound
  exact ((ha.stronglyMeasurable_stopped_jump_of_usual hF hc hτ).mono
    hτ.measurableSpace_le).aestronglyMeasurable

end ProbabilityTheory
