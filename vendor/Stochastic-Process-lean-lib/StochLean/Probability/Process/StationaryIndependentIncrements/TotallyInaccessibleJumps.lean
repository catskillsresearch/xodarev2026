/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrements.StoppingWindow
public import StochLean.Probability.Process.StationaryIncrementsCompletion
public import StochLean.Probability.Process.Stopping.SmallWindowSampling
public import StochLean.Probability.Process.Stopping.AnnouncingJumpLimit
public import StochLean.Probability.Process.Stopping.FiniteSampleMeasurability
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumpTests
public import StochLean.Probability.Process.IndependentIncrements.NaturalFiltration
public import StochLean.Probability.Process.Filtration.IndependentIncrementsAugmentation

/-! # Totally inaccessible jumps of stationary independent increments

At a genuinely finite predictable time, actual finite announcing times approach
from the left and their sampled increments converge almost surely to the
positive-time jump. Stationary independent increments identify a uniform
post-stopping small-window bound with the original window at zero. Right
continuity makes those reference-window tails vanish, so the same sampled
increments converge in measure to zero. Uniqueness of limits in measure forces
the predictable jump to vanish.

Integer truncations pass from finite predictable times to arbitrary predictable
tests. The existing predictable-test classification then supplies the actual
countable totally-inaccessible jump covering. The final entry point constructs
the genuine completed usual natural filtration of a zero-initial cadlag
stationary-independent-increment process. No Markov/Feller certificate, moments,
alternate process realization, or arbitrary information enlargement is used.
The zero-initial hypothesis at the natural-filtration entry is essential:
stationary independent increments alone do not prevent the initial value from
revealing future jump information.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual positive-time jump at a genuinely finite predictable time
vanishes for a right-continuous process with stationary increments independent
of the specified past. The zero-time source jump is explicitly excluded. -/
theorem HasStationaryIncrements.ae_jumpProcess_eq_zero_at_finite_predictable
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hc : HasCadlagPaths X P) (τ : FiniteStoppingTime F)
    (hτ : IsPredictableStoppingTime F τ.withTop P) :
    ∀ᵐ ω ∂P, 0 < τ ω → jumpProcess X (τ ω) ω = 0 := by
  obtain ⟨σ, hle, hlim, hjump⟩ := hτ.exists_finite_announcing_jump_limit hc
  let d : ℕ → ℝ≥0 := fun k ↦ 1 / ((k : ℝ≥0) + 1)
  let b : ℝ → ℕ → ℝ≥0∞ := fun ε k ↦
    P {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X u ω - X 0 ω‖) (d k) ω}
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun k : ℕ ↦ 1 / ((k : ℝ≥0) + 1)) atTop (𝓝 0))
  have hb (ε : ℝ) (hε : 0 < ε) : Tendsto (b ε) atTop (𝓝 0) :=
    hc.hasRightContinuousPaths.tendsto_measure_denseRunningSupremum_norm_sub_initial
      (fun _ ↦ ha.measurable) hd hε
  have hwin (ε : ℝ) (hε : 0 < ε) (n k : ℕ) :
      P {ω | ENNReal.ofReal ε < denseRunningSupremum
        (fun u ω ↦ ‖X (σ n ω + u) ω - X (σ n ω) ω‖) (d k) ω} ≤ b ε k := by
    exact le_of_eq (hs.measure_denseRunningSupremum_norm_after_eq
      ha hi hc.hasRightContinuousPaths (σ n) (d k) ε)
  have hzero : TendstoInMeasure P
      (fun n ω ↦ X (τ ω) ω - X (σ n ω) ω) atTop (fun _ ↦ (0 : ℝ)) :=
    tendstoInMeasure_sub_sample_of_small_window_bound hc.hasRightContinuousPaths
      τ σ (fun n ↦ ae_of_all P (hle n)) hlim b hb hwin
  have hmτ := τ.aemeasurable_sample_of_rightContinuous
    (P := P) (fun _ ↦ ha.measurable) hc.hasRightContinuousPaths
  have hmσ (n : ℕ) := (σ n).aemeasurable_sample_of_rightContinuous
    (P := P) (fun _ ↦ ha.measurable) hc.hasRightContinuousPaths
  have hjumpMeasure : TendstoInMeasure P
      (fun n ω ↦ X (τ ω) ω - X (σ n ω) ω) atTop
      (fun ω ↦ if τ ω = 0 then 0 else jumpProcess X (τ ω) ω) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (hmτ.sub (hmσ n)).aestronglyMeasurable) hjump
  have he := tendstoInMeasure_ae_unique hjumpMeasure hzero
  filter_upwards [he] with ω hω hpos
  simpa only [if_neg (ne_of_gt hpos)] using hω

/-- Every predictable test has zero jump on its positive finite graph.
Integer truncations are genuine finite predictable times; their fixed cap
jumps are also controlled by the same stationary-window argument. -/
theorem HasStationaryIncrements.ae_jumpProcess_eq_zero_at_predictable_of_indep_past
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hc : HasCadlagPaths X P) {γ : Ω → WithTop ℝ≥0}
    (hγ : IsPredictableStoppingTime F γ P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω = (t : WithTop ℝ≥0) →
      jumpProcess X t ω = 0 := by
  let τ (n : ℕ) : FiniteStoppingTime F :=
    FiniteStoppingTime.truncate hγ.1 (n : ℝ≥0)
  have hτpred (n : ℕ) : IsPredictableStoppingTime F (τ n).withTop P := by
    have hmin := (isPredictableStoppingTime_const F P (n : ℝ≥0)).min hγ
    simpa only [τ, FiniteStoppingTime.withTop_truncate] using hmin
  have hzero (n : ℕ) :
      ∀ᵐ ω ∂P, 0 < τ n ω → jumpProcess X (τ n ω) ω = 0 :=
    hs.ae_jumpProcess_eq_zero_at_finite_predictable ha hi hc (τ n) (hτpred n)
  have hall : ∀ᵐ ω ∂P, ∀ n, 0 < τ n ω →
      jumpProcess X (τ n ω) ω = 0 := ae_all_iff.mpr hzero
  filter_upwards [hall] with ω hω
  intro t ht hγt
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hτeq : τ n ω = t := by
    apply WithTop.coe_eq_coe.mp
    change (τ n).withTop ω = (t : WithTop ℝ≥0)
    rw [FiniteStoppingTime.withTop_truncate]
    simp only [hγt, min_eq_right (WithTop.coe_le_coe.mpr hn)]
  rw [← hτeq]
  exact hω n (hτeq ▸ ht)

/-- A cadlag process with stationary increments independent of its specified
past has totally inaccessible positive-time jumps under usual conditions. -/
theorem HasStationaryIncrements.hasTotallyInaccessibleJumps_of_indep_past
    (hs : HasStationaryIncrements X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    HasTotallyInaccessibleJumps F X P :=
  ha.hasTotallyInaccessibleJumps_of_predictable_tests hF hc
    (fun _ hγ ↦ hs.ae_jumpProcess_eq_zero_at_predictable_of_indep_past ha hi hc hγ)

/-- A zero-initial cadlag real stationary-independent-increment process has
totally inaccessible jumps in the genuine completed usual augmentation of
its original natural filtration. The process itself is not replaced. -/
theorem HasStationaryIndependentIncrements.hasTotallyInaccessibleJumps_natural_usualAugmentation
    (hX : HasStationaryIndependentIncrements X P) (hXm : ∀ t, Measurable (X t))
    (hX0 : X 0 =ᵐ[P] 0) (hc : HasCadlagPaths X P) :
    HasTotallyInaccessibleJumps
      ((Filtration.natural X (fun t ↦ (hXm t).stronglyMeasurable)).usualAugmentation P)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) P.completion := by
  let G := Filtration.natural X (fun t ↦ (hXm t).stronglyMeasurable)
  have ha : Adapted G X := (Filtration.stronglyAdapted_natural _).adapted
  have hi : ∀ s t, s ≤ t → Indep (G s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P :=
    fun _ _ hst ↦ hX.indepIncrements.indep_increment_natural hXm hX0 hst
  have hiAug : ∀ s t, s ≤ t →
      Indep (G.usualAugmentation P s)
        (MeasurableSpace.comap
          (fun ω : NullMeasurableSpace Ω P ↦ X t ω - X s ω) inferInstance)
        P.completion :=
    fun _ _ hst ↦ hc.hasRightContinuousPaths.indep_increment_usualAugmentation
      ha hi hst
  have hcComp : HasCadlagPaths
      (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) P.completion := hc
  exact hX.stationaryIncrements.completion.hasTotallyInaccessibleJumps_of_indep_past
    (ha.usualAugmentation P) hiAug (G.usualAugmentation_isUsual P) hcComp

end ProbabilityTheory
