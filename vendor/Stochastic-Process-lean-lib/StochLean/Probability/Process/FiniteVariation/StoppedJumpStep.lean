/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import StochLean.Probability.Process.Path.JumpSampling
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Analysis.PathVariation.StieltjesPureJumpIntegral

/-! # A single step carrying the actual jump at a stopping time

The coefficient is the zero-terminal stopped jump of the original process and
is revealed at, not before, the stopping time.  For a positive stopping time,
local integrable variation of the source localizes the single step: on each
source localizer its coefficient is the corresponding jump of the stopped
source process.  This is the finite-variation input needed by the
Lenglart--Girsanov correction.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The closed step at `τ` whose coefficient is the actual jump of `X` at
`τ`; an infinite time has the explicit terminal coefficient zero. -/
noncomputable def stoppedJumpStep (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ)

/-- The stopped-jump step has exactly its sampled coefficient on the finite
lifetime graph and no other jumps. -/
theorem jumpProcess_stoppedJumpStep (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    jumpProcess (stoppedJumpStep X τ) t ω =
      {ω | τ ω = (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) ω := by
  exact jumpProcess_indicator_lifetime_le τ
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) t ω

/-- Before activation the left value is zero; after activation it is the
sampled jump coefficient. -/
theorem leftLimitProcess_stoppedJumpStep (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess (stoppedJumpStep X τ) t ω =
      {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) ω := by
  exact leftLimitProcess_indicator_lifetime_le τ
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) t ω

/-- Stopped-field measurability reveals the coefficient exactly when the step
is activated. -/
theorem Adapted.adapted_stoppedJumpStep_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Adapted F (stoppedJumpStep X τ) := by
  intro t
  exact (ha.stronglyMeasurable_stopped_jump_of_usual hF hc hτ
    |>.indicator_stoppingTime_le hτ t).measurable

/-- A single closed lifetime step is càdlà, including at zero and infinity. -/
theorem hasCadlagPaths_stoppedJumpStep (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : HasCadlagPaths (stoppedJumpStep X τ) P := by
  exact ae_of_all P (isCadlagPath_indicator_lifetime_le τ
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ))

/-- The pathwise Stieltjes integral against a positive-time stopped-jump
step is the integrand sampled at that jump, multiplied by the jump
coefficient and activated from the jump time onward. -/
theorem pathStieltjesIntegral_stoppedJumpStep_of_eq_coe
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω)
    {r : ℝ≥0} (hrpos : 0 < r) (hτ : τ ω = (r : WithTop ℝ≥0))
    (hv : LocallyBoundedVariationOn (stoppedJumpStep X τ · ω) univ)
    (hr : IsRightContinuousPath (stoppedJumpStep X τ · ω))
    (H : ℝ≥0 → ℝ) (hH : Measurable H) (t : ℝ≥0)
    {C : ℝ} (hC : ∀ s ∈ Ioc 0 t, ‖H s‖ ≤ C) :
    pathStieltjesIntegral (stoppedJumpStep X τ · ω) hv hr H t =
      if r ≤ t then H r * jumpProcess X r ω else 0 := by
  let U := stoppedJumpStep X τ
  let c := jumpProcess X r ω
  have hUval (s : ℝ≥0) : U s ω = if r ≤ s then c else 0 := by
    simp only [U, stoppedJumpStep, indicator_apply, mem_ofPred_eq, hτ,
      WithTop.coe_le_coe, stoppedValueWithTerminal_jump_eq_of_eq_coe hτ, c]
  have hUzero : U 0 ω = 0 := by
    rw [hUval]
    simp [not_le_of_gt hrpos]
  have hUjump (s : ℝ≥0) : jumpProcess U s ω = if r = s then c else 0 := by
    rw [jumpProcess_stoppedJumpStep]
    simp only [indicator_apply, mem_ofPred_eq, hτ, WithTop.coe_eq_coe,
      stoppedValueWithTerminal_jump_eq_of_eq_coe hτ, c]
  have hpure (s : ℝ≥0) : U s ω - U 0 ω =
      ∑' u : Ioc 0 s, jumpProcess U u ω := by
    by_cases hrs : r ≤ s
    · let q : Ioc (0 : ℝ≥0) s := ⟨r, hrpos, hrs⟩
      rw [tsum_eq_single q]
      · rw [hUval, if_pos hrs, hUzero]
        have hq : (q : ℝ≥0) = r := rfl
        rw [hUjump, hq, if_pos rfl, sub_zero]
      · intro q' hne
        rw [hUjump, if_neg]
        intro heq
        apply hne
        apply Subtype.ext
        exact heq.symm
    · rw [hUval, if_neg hrs, hUzero, sub_zero]
      rw [show (fun u : Ioc 0 s ↦ jumpProcess U u ω) = (fun _ ↦ 0) by
        funext q
        rw [hUjump, if_neg]
        intro heq
        exact hrs (heq ▸ q.2.2), tsum_zero]
  have hpure' (s : ℝ≥0) : U s ω - U 0 ω =
      ∑' u : Ioc 0 s, (U u ω - Function.leftLim (U · ω) u) := by
    rw [hpure]
    apply tsum_congr
    intro u
    simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg u.2.1.ne']
  rw [pathStieltjesIntegral_eq_initial_add_tsum_of_pureJump
    hv hr hpure' t hH hC]
  change H 0 * U 0 ω +
      (∑' s : Ioc 0 t, H s * (U s ω - Function.leftLim (U · ω) s)) = _
  rw [hUzero, mul_zero, zero_add]
  have hsum : (∑' s : Ioc 0 t,
      H s * (U s ω - Function.leftLim (U · ω) s)) =
      ∑' s : Ioc 0 t, H s * jumpProcess U s ω := by
    apply tsum_congr
    intro s
    simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg s.2.1.ne']
  rw [hsum]
  by_cases hrt : r ≤ t
  · rw [if_pos hrt]
    let q : Ioc (0 : ℝ≥0) t := ⟨r, hrpos, hrt⟩
    rw [tsum_eq_single q]
    · have hq : (q : ℝ≥0) = r := rfl
      rw [hUjump, hq, if_pos rfl]
    · intro q' hne
      rw [hUjump, if_neg, mul_zero]
      intro heq
      apply hne
      apply Subtype.ext
      exact heq.symm
  · rw [if_neg hrt]
    rw [show (fun u : Ioc 0 t ↦ H u * jumpProcess U u ω) = (fun _ ↦ 0) by
      funext q
      rw [hUjump, if_neg, mul_zero]
      intro heq
      exact hrt (heq ▸ q.2.2), tsum_zero]

/-- Local integrable variation of the source controls the actual stopped-jump
step at every strictly positive stopping time. -/
theorem HasLocallyIntegrableVariation.stoppedJumpStep_hasLocallyIntegrableVariation
    (hv : HasLocallyIntegrableVariation X F P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hpos : ∀ ω, 0 < τ ω) :
    HasLocallyIntegrableVariation (stoppedJumpStep X τ) F P := by
  obtain ⟨ρ, hρ, hvρ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hv
  apply hasLocallyIntegrableVariation_iff_exists_stopped.mpr
  refine ⟨ρ, hρ, fun n ↦ ?_⟩
  let Xn := stoppedProcess X (ρ n)
  let J := stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ
  let Cn := {ω | τ ω ≤ ρ n ω}.indicator J
  have haXn : Adapted F Xn :=
    (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths
      (hρ.isStoppingTime n)).adapted
  have hcXn : HasCadlagPaths Xn P := hc.stoppedProcess (ρ n)
  have hiXn : Integrable
      (stoppedValueWithTerminal (jumpProcess Xn) (fun _ ↦ (0 : ℝ)) τ) P :=
    (hvρ n).integrable_stopped_jump haXn hF hcXn hτ (ae_of_all P hpos)
  have heCoeff :
      stoppedValueWithTerminal (jumpProcess Xn) (fun _ ↦ (0 : ℝ)) τ =ᵐ[P] Cn := by
    simpa only [Xn, J, Cn, indicator_univ] using
      (hc.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess
        (Set.univ : Set Ω) (ρ n) τ)
  have hiCn : Integrable Cn P := hiXn.congr heCoeff
  have heStop : stoppedProcess (ProbabilityTheory.stoppedJumpStep X τ) (ρ n) =
      fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Cn := by
    funext t ω
    classical
    have hne : min (t : WithTop ℝ≥0) (ρ n ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hcoe :
        (((min (t : WithTop ℝ≥0) (ρ n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) =
          min (t : WithTop ℝ≥0) (ρ n ω) := by
      rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
    simp only [stoppedProcess, stoppedJumpStep, indicator_apply, mem_ofPred_eq,
      Cn, J, hcoe, le_min_iff]
    by_cases ht : τ ω ≤ (t : WithTop ℝ≥0) <;>
      by_cases hr : τ ω ≤ ρ n ω <;> simp [ht, hr]
  rw [heStop]
  exact hasIntegrableVariation_indicator_lifetime_le hτ.measurable' hiCn

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The original zero-terminal left-limit sample is measurable in the
before-field of an arbitrary stopping time.  Usual completeness transfers the
claim from an everywhere left-continuous predictable version. -/
theorem Adapted.stronglyMeasurable_stopped_leftLimit_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpaceBefore]
      (stoppedValueWithTerminal (leftLimitProcess X) (fun _ ↦ (0 : ℝ)) τ) := by
  obtain ⟨Y, heq, hpY, _⟩ := ha.exists_predictable_leftLimitProcess_of_usual hF hc
  have hmY : StronglyMeasurable[hτ.measurableSpaceBefore]
      (stoppedValueWithTerminal Y (fun _ ↦ (0 : ℝ)) τ) :=
    hpY.stronglyMeasurable_stoppedValueWithTerminal_before
      (Z := fun _ ↦ (0 : ℝ)) stronglyMeasurable_const hτ
  have hcomplete : IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore :=
    fun s hs ↦ hτ.le_measurableSpaceBefore s (hF.complete_initial s hs)
  exact (hcomplete.measurable_congr_ae hmY.measurable
    (heq.stoppedValueWithTerminal (EventuallyEq.refl _ _) τ).symm).stronglyMeasurable

end MeasureTheory
