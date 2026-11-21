/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJumpContinuous
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra
public import StochLean.Probability.Process.FiniteVariation.MonotoneIntegrable
public import StochLean.Probability.Process.LocalMartingale.Reducing

/-! # Compensation of a signed totally inaccessible single jump

The existing nonnegative-amplitude construction is applied to the positive
and negative parts of the actual stopped-measurable coefficient. The difference
of the resulting compensators has everywhere continuous paths, is predictable,
and starts exactly at zero. No compensator or terminal random variable is an
input to the final theorem.

The actual increasing terminal envelopes bound the canonical whole-half-line
variations. Finiteness is established before conversion to real values. Their
first-moment bounds give the sharp bound by the original absolute first moment.
The compensated signed jump is an actual uniformly integrable martingale.
Infinite lifetimes are allowed and never activate at a finite time.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {D : Ω → ℝ}

omit [IsProbabilityMeasure P] in
private theorem integrableVariation_of_monotone_terminal_bound
    {B : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (ha : Adapted F B) (hF : F.IsUsual P) (hc : ∀ ω, Continuous (B · ω))
    (h0 : B 0 = 0) (hm : HasMonotonePaths B P) (hiZ : Integrable Z P)
    (hb : ∀ᵐ ω ∂P, ∀ t, 0 ≤ B t ω ∧ B t ω ≤ Z ω) :
    HasIntegrableVariation B P ∧
      (∫ ω, (eVariationOn (B · ω) univ).toReal ∂P) ≤ ∫ ω, Z ω ∂P := by
  exact hm.hasIntegrableVariation_of_integrable_bound ha hF
    (show HasContinuousPaths B P from ae_of_all _ hc).hasCadlagPaths
    (Eventually.of_forall fun ω ↦ congrFun h0 ω) hiZ hb

/-- An arbitrary integrable signed jump at a totally inaccessible lifetime has
an actual continuous predictable compensator of integrable total variation.
The expected total variation is bounded by the coefficient's first norm moment.
The lifetime need not be finite. -/
theorem IsTotallyInaccessibleStoppingTime.exists_continuous_compensator_indicator
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] D) (hi : Integrable D P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasIntegrableVariation A P ∧
      (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖D ω‖ ∂P ∧
      IsUIMartingale
        ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator D) - A) F P := by
  classical
  let Dp : Ω → ℝ := fun ω ↦ max (D ω) 0
  let Dn : Ω → ℝ := fun ω ↦ max (-D ω) 0
  have hmp : StronglyMeasurable[hτ.1.measurableSpace] Dp := by
    let : MeasurableSpace Ω := hτ.1.measurableSpace
    exact hm.sup stronglyMeasurable_const
  have hmn : StronglyMeasurable[hτ.1.measurableSpace] Dn := by
    let : MeasurableSpace Ω := hτ.1.measurableSpace
    exact hm.neg.sup stronglyMeasurable_const
  have hi0 : Integrable (0 : Ω → ℝ) P :=
    ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
  have hip : Integrable Dp P := hi.sup hi0
  have hin : Integrable Dn P := hi.neg.sup hi0
  have hnp : ∀ᵐ ω ∂P, 0 ≤ Dp ω := ae_of_all _ fun _ ↦ le_max_right _ _
  have hnn : ∀ᵐ ω ∂P, 0 ≤ Dn ω := ae_of_all _ fun _ ↦ le_max_right _ _
  have hsub (ω : Ω) : Dp ω - Dn ω = D ω := by
    by_cases hω : 0 ≤ D ω
    · simp only [Dp, Dn, max_eq_left hω, max_eq_right (neg_nonpos.mpr hω), sub_zero]
    · simp only [Dp, Dn, max_eq_right (le_of_not_ge hω),
        max_eq_left (neg_nonneg.mpr (le_of_not_ge hω)), zero_sub, neg_neg]
  have hadd (ω : Ω) : Dp ω + Dn ω = ‖D ω‖ := by
    by_cases hω : 0 ≤ D ω
    · simp only [Dp, Dn, max_eq_left hω, max_eq_right (neg_nonpos.mpr hω), add_zero,
        Real.norm_of_nonneg hω]
    · simp only [Dp, Dn, max_eq_right (le_of_not_ge hω),
        max_eq_left (neg_nonneg.mpr (le_of_not_ge hω)), zero_add,
        Real.norm_of_nonpos (le_of_not_ge hω)]
  obtain ⟨Bp, Zp, _, hap, _, hcp, h0p, hmonp, _, _, hiZp, hEZp, hbp,
      _, _, hMp, _, _, hUIp, _⟩ :=
    hτ.exists_continuous_compensator_neg hF hmp hip hnp
  obtain ⟨Bn, Zn, _, han, _, hcn, h0n, hmonn, _, _, hiZn, hEZn, hbn,
      _, _, hMn, _, _, hUIn, _⟩ :=
    hτ.exists_continuous_compensator_neg hF hmn hin hnn
  obtain ⟨hvp, hEVp⟩ :=
    integrableVariation_of_monotone_terminal_bound hap hF hcp h0p hmonp hiZp hbp
  obtain ⟨hvn, hEVn⟩ :=
    integrableVariation_of_monotone_terminal_bound han hF hcn h0n hmonn hiZn hbn
  let A : ℝ≥0 → Ω → ℝ := Bp - Bn
  have haA : Adapted F A := fun t ↦ (hap t).sub (han t)
  have hcA (ω : Ω) : Continuous (A · ω) := (hcp ω).sub (hcn ω)
  have hcadp : HasCadlagPaths Bp P :=
    (show HasContinuousPaths Bp P from ae_of_all _ hcp).hasCadlagPaths
  have hcadn : HasCadlagPaths Bn P :=
    (show HasContinuousPaths Bn P from ae_of_all _ hcn).hasCadlagPaths
  have hvA : HasIntegrableVariation A P := hvp.sub hvn hap han hF hcadp hcadn
  have hEV : (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖D ω‖ ∂P := by
    calc
      _ ≤ ∫ ω, (eVariationOn (Bp · ω) univ).toReal +
          (eVariationOn (Bn · ω) univ).toReal ∂P := by
        apply integral_mono_ae hvA.integrable_eVariationOn_toReal
          (hvp.integrable_eVariationOn_toReal.add hvn.integrable_eVariationOn_toReal)
        filter_upwards [hvp.ae_eVariationOn_ne_top, hvn.ae_eVariationOn_ne_top] with ω hp hn
        have hbound : eVariationOn (A · ω) univ ≤
            eVariationOn (Bp · ω) univ + eVariationOn (Bn · ω) univ := by
          simpa only [A, Pi.sub_apply, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply,
            eVariationOn_neg] using
            eVariationOn_add_le (Bp · ω) (fun t ↦ -Bn t ω) univ
        simpa only [ENNReal.toReal_add hp hn, Pi.add_apply] using
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hp, hn⟩) hbound
      _ = (∫ ω, (eVariationOn (Bp · ω) univ).toReal ∂P) +
          ∫ ω, (eVariationOn (Bn · ω) univ).toReal ∂P :=
        integral_add hvp.integrable_eVariationOn_toReal hvn.integrable_eVariationOn_toReal
      _ ≤ (∫ ω, Dp ω ∂P) + ∫ ω, Dn ω ∂P :=
        add_le_add (hEVp.trans hEZp) (hEVn.trans hEZn)
      _ = ∫ ω, ‖D ω‖ ∂P := by
        rw [← integral_add hip hin]
        exact integral_congr_ae (ae_of_all _ hadd)
  have hUMp : IsUIMartingale
      ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Dp ω)) + Bp)
      F P := ⟨hMp, hUIp⟩
  have hUMn : IsUIMartingale
      ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Dn ω)) + Bn)
      F P := ⟨hMn, hUIn⟩
  refine ⟨A, haA,
    haA.isStronglyPredictable_of_leftContinuous (fun ω _ ↦ (hcA ω).continuousWithinAt),
    hcA, ?_, hvA, hEV, ?_⟩
  · funext ω
    change Bp 0 ω - Bn 0 ω = 0
    simp only [h0p, h0n, Pi.zero_apply, sub_self]
  · have he :
        (((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Dn ω)) + Bn) -
          ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -Dp ω)) + Bp)) =
        ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator D) - A) := by
      funext t ω
      simp only [Pi.sub_apply, Pi.add_apply, A, indicator_apply, mem_ofPred_eq]
      by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
      · simp only [if_pos ht]
        linarith [hsub ω]
      · simp only [if_neg ht]
        ring
    rw [← he]
    exact hUMn.sub hUMp

end ProbabilityTheory
