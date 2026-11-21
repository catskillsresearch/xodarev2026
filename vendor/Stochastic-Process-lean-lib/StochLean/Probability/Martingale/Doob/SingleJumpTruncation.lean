/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJump
public import StochLean.Probability.Martingale.Doob.ContinuousBounded

/-! # Actual continuous compensators for clipped single jumps

For a nonnegative integrable coefficient C, the negative jump with coefficient
`-min C R` is bounded by R. Ordered clipping differences are again negative
single jumps and hence actual supermartingales. The existing bounded Doob
theorem constructs their continuous compensators; none is supplied as input.
The remaining amplitude `C - min C n` has mean tending to zero.

This clipping convention avoids confusing an unbounded large-amplitude tail
with the bounded part in the printed argument on Protter p.112.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {C : Ω → ℝ}

omit [IsFiniteMeasure P] in
/-- The mean of the actual nonnegative clipping error tends to zero. -/
theorem Integrable.tendsto_integral_sub_min_nat (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) :
    Tendsto (fun n : ℕ ↦ ∫ ω, C ω - min (C ω) (n : ℝ) ∂P) atTop (𝓝 0) := by
  have hlim (ω : Ω) :
      Tendsto (fun n : ℕ ↦ C ω - min (C ω) (n : ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (C ω)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [min_eq_left (hN.le.trans (Nat.cast_le.mpr hn)), sub_self]
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖C ω - min (C ω) (n : ℝ)‖ ≤ C ω := by
    filter_upwards [hn] with ω hω
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
    exact sub_le_self _ (le_min hω (Nat.cast_nonneg _))
  simpa only [integral_zero, Pi.sub_apply, Pi.inf_apply] using
    tendsto_integral_of_dominated_convergence C
      (fun n ↦ hi.aestronglyMeasurable.sub
        (hi.aestronglyMeasurable.inf aestronglyMeasurable_const)) hi hb
      (Eventually.of_forall hlim)

/-- Clipping a nonnegative amplitude gives a bounded negative-jump supermartingale. -/
theorem supermartingale_indicator_stoppingTime_le_neg_min
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] C)
    (hi : Integrable C P) (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) {R : ℝ} (hR : 0 ≤ R) :
    Supermartingale (fun t : ℝ≥0 ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -min (C ω) R)) F P := by
  have hmR : StronglyMeasurable[hτ.measurableSpace] (fun ω ↦ -min (C ω) R) := by
    let : MeasurableSpace Ω := hτ.measurableSpace
    exact (hm.inf stronglyMeasurable_const).neg
  apply supermartingale_indicator_stoppingTime_le hτ hmR (hi.inf (integrable_const R)).neg
  exact hn.mono fun _ hω ↦ neg_nonpos.mpr (le_min hω hR)

/-- Ordered clipping differences, not mere pointwise process order, supply
the supermartingale hypothesis needed for compensator comparison. -/
theorem supermartingale_indicator_stoppingTime_le_neg_min_sub
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] C)
    (hi : Integrable C P) {R S : ℝ} (hRS : R ≤ S) :
    Supermartingale (fun t : ℝ≥0 ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
        (fun ω ↦ -min (C ω) S - -min (C ω) R)) F P := by
  have hmR : StronglyMeasurable[hτ.measurableSpace] (fun ω ↦ -min (C ω) R) := by
    let : MeasurableSpace Ω := hτ.measurableSpace
    exact (hm.inf stronglyMeasurable_const).neg
  have hmS : StronglyMeasurable[hτ.measurableSpace] (fun ω ↦ -min (C ω) S) := by
    let : MeasurableSpace Ω := hτ.measurableSpace
    exact (hm.inf stronglyMeasurable_const).neg
  apply supermartingale_indicator_stoppingTime_le hτ (hmS.sub hmR)
    ((hi.inf (integrable_const S)).neg.sub (hi.inf (integrable_const R)).neg)
  exact Eventually.of_forall fun _ ↦ sub_nonpos.mpr
    (neg_le_neg (min_le_min le_rfl hRS))

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {C : Ω → ℝ}

/-- The clipped single-jump compensator is constructed by the actual bounded
Doob theorem, retaining its actual L2 closing variable and dyadic UCP limit. -/
theorem IsTotallyInaccessibleStoppingTime.exists_continuous_compensator_neg_min
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hF : F.IsUsual P) (hm : StronglyMeasurable[hτ.1.measurableSpace] C)
    (hi : Integrable C P) (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) {R : ℝ} (hR : 0 ≤ R) :
    let X : ℝ≥0 → Ω → ℝ := fun t ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun ω ↦ -min (C ω) R)
    ∃ (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      MemLp L 2 P ∧ (∀ t, X t + A t =ᵐ[P] P[L | F t]) ∧
      Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧
      (∀ t, MemLp (A t) 2 P ∧ MemLp (X t + A t) 2 P) ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  intro X
  have hX : Supermartingale X F P :=
    supermartingale_indicator_stoppingTime_le_neg_min hτ.1 hm hi hn hR
  have hc : HasCadlagPaths X P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le τ (fun ω ↦ -min (C ω) R))
  apply hX.exists_continuous_doob_decomposition_of_bound hF hc
    (hτ.hasTotallyInaccessibleJumps_indicator _) hR
  filter_upwards [hn] with ω hω t
  apply (norm_indicator_le_norm_self _ _).trans
  rw [norm_neg, Real.norm_of_nonneg (le_min hω hR)]
  exact min_le_right _ _

end ProbabilityTheory
