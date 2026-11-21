/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.NaturalStopping
public import StochLean.Probability.Martingale.CovariationExpectation
public import StochLean.Probability.Martingale.Doob.ConditionalEnvelope

/-! # A natural finite-variation martingale is zero

Protter III.13 is proved with actual bounded conditional martingales. At a
fixed time `T`, regularization constructs the cadlag martingale closed by
the indicator of `{A T > 0}`. Naturality and the independently proved raw
mixed-sum expectation identity force the positive part of `A T` to vanish.
The original martingale's zero initial mean then forces `A T` itself to
vanish. Right continuity upgrades these coordinate conclusions to equality
of entire paths on one common event.

Only L1 integrability of the original martingale is used. In particular no
L2 property of `A`, martingale property of its mixed bracket, or predictable
jump enumeration is an extra premise.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ} {hF : F.IsUsual P}

/-- Every deterministic coordinate of a natural martingale is zero. The
bounded test martingale is constructed, not supplied as a certificate. -/
theorem IsNatural.ae_eq_zero_of_martingale (hN : IsNatural A F P hF)
    (hA : Martingale A F P) (T : ℝ≥0) : A T =ᵐ[P] 0 := by
  let E : Set Ω := {ω | 0 < A T ω}
  have hE : MeasurableSet[F T] E := measurableSet_lt measurable_const (hN.adapted T)
  have hEm : MeasurableSet E := F.le T E hE
  let D : Ω → ℝ := E.indicator (fun _ ↦ (1 : ℝ))
  have hDm : StronglyMeasurable[F T] D :=
    (measurable_const.indicator hE).stronglyMeasurable
  have hDlp : MemLp D 2 P := (memLp_const (1 : ℝ)).indicator hEm
  have hD0 : 0 ≤ᵐ[P] D :=
    ae_of_all _ fun ω ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) ω
  have hD1 : D ≤ᵐ[P] fun _ ↦ (1 : ℝ) := by
    filter_upwards with ω
    by_cases hω : ω ∈ E
    · exact (indicator_of_mem hω _).le
    · have hz : D ω = 0 := indicator_of_notMem hω _
      rw [hz]
      exact zero_le_one
  obtain ⟨H, hH, hcH, heH, hnH, _⟩ := exists_cadlag_conditionalEnvelope hF hDlp hD0
  have hupper : ∀ t : ℝ≥0, H t ≤ᵐ[P] fun _ ↦ (1 : ℝ) := fun t ↦
    (heH t).trans_le (condExp_le_nonneg_const (m := F t) zero_le_one hD1)
  have huH := hcH.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le
    (ae_of_all _ fun _ _ ↦ continuousWithinAt_const) hupper
  have hbH : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hnH, huH] with ω hn hu t
    rw [Real.norm_of_nonneg (hn t)]
    exact hu t
  have hHT : H T =ᵐ[P] D := by
    simpa only [condExp_of_stronglyMeasurable (F.le T) hDm
      (hDlp.integrable (by norm_num))] using heH T
  have hqzero := hN.integrable_quadraticCovariation_and_integral_eq_zero
    hH hcH 1 zero_le_one hbH T
  have hqmean := hH.integrable_quadraticCovariation_and_integral_eq_of_integrableVariation
    hA hF hcH hN.hasCadlagPaths hN.hasIntegrableVariation 1 zero_le_one hbH T
  have hpair : (∫ ω, H T ω * A T ω ∂P) = 0 := hqmean.2.symm.trans hqzero.2
  have hprod : (fun ω ↦ H T ω * A T ω) =ᵐ[P] E.indicator (A T) := by
    filter_upwards [hHT] with ω hω
    rw [hω]
    by_cases hmem : ω ∈ E
    · simp only [D, indicator_of_mem hmem, one_mul]
    · simp only [D, indicator_of_notMem hmem, zero_mul]
  have hipos : Integrable (E.indicator (A T)) P := (hA.integrable T).indicator hEm
  have hnpos : 0 ≤ᵐ[P] E.indicator (A T) := by
    filter_upwards with ω
    exact indicator_nonneg (fun v hv ↦ (show 0 < A T v from hv).le) ω
  have hzpos : E.indicator (A T) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnpos hipos).mp
      ((integral_congr_ae hprod).symm.trans hpair)
  have hnonpos : A T ≤ᵐ[P] 0 := by
    filter_upwards [hzpos] with ω hω
    change A T ω ≤ 0
    by_contra hnot
    have hmem : ω ∈ E := lt_of_not_ge hnot
    rw [indicator_of_mem hmem] at hω
    change A T ω = 0 at hω
    exact hnot hω.le
  have hmeanA : (∫ ω, A T ω ∂P) = 0 := by
    have hm := hA.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T)
      (@MeasurableSet.univ Ω (F 0))
    rw [setIntegral_univ, setIntegral_univ] at hm
    calc
      (∫ ω, A T ω ∂P) = ∫ ω, A 0 ω ∂P := hm.symm
      _ = 0 := by
        simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hN.zero_ae
  apply (integral_eq_iff_of_ae_le (hA.integrable T) (integrable_zero Ω ℝ P) hnonpos).mp
  simpa only [Pi.zero_apply, integral_zero] using hmeanA

/-- Protter III.13: a natural process which is a martingale vanishes on one
common full-measure event at every time, not merely separately at each time. -/
theorem IsNatural.indistinguishable_zero_of_martingale (hN : IsNatural A F P hF)
    (hA : Martingale A F P) : Indistinguishable A 0 P := by
  have he : IsModification A 0 P := hN.ae_eq_zero_of_martingale hA
  exact he.indistinguishable_of_rightContinuous hN.hasCadlagPaths.hasRightContinuousPaths
    (ae_of_all _ fun _ _ ↦ continuousWithinAt_const)

end ProbabilityTheory
