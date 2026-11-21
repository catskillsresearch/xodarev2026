/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.PartitionDependence
public import StochLean.Analysis.PathVariation.Restriction
public import StochLean.Probability.Process.Filtration.IndependentIncrementsAugmentation
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann

/-! # A continuous adapted zero-QV path which is not a semimartingale

This closes the counterexample side of regression R36.  We use the project-owned
continuous path whose quadratic sums have limits zero and one along two
admissible deterministic partition sequences.  The path is made into a
deterministic process on a completed one-point probability space.

If that process were a semimartingale, random-partition approximation of its
canonical raw quadratic variation would force both deterministic square-sum
sequences to have the same limit in probability.  Since on a one-point space
the pathwise limits are respectively zero and one, uniqueness of limits in
measure gives a contradiction.  Thus no decomposition theorem, and no
unproved classification of local martingales on a one-point space, is used.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory.R36Counterexample

/-- The path and the two incompatible quadratic-variation computations used
by the R36 counterexample. -/
structure PathWitness where
  path : ℝ≥0 → ℝ
  zeroPartition : ℕ → LocallyFinitePartition
  continuous_path : Continuous path
  zeroPartition_admissible : IsAdmissiblePartitionSequence zeroPartition
  zero_quadraticVariation :
    HasQuadraticVariationAlong (fun n ↦ (zeroPartition n).restrict 1) path 0
  one_quadraticVariation :
    HasQuadraticVariationAlong
      (fun n ↦ (LocallyFinitePartition.dyadic n).restrict 1) path 1

/-- The partition-dependence theorem supplies an inhabitant without eliminating
its existential proposition directly into data. -/
theorem pathWitness_nonempty : Nonempty PathWitness := by
  obtain ⟨x, π, hx, hπ, hzero, hone⟩ :=
    exists_continuous_partition_dependent_quadraticVariation
  exact ⟨⟨x, π, hx, hπ, hzero, hone⟩⟩

/-- A fixed project-internal continuous path with partition-dependent
quadratic variation. -/
noncomputable def pathWitness : PathWitness :=
  Classical.choice pathWitness_nonempty

/-- The one-point probability measure supporting the deterministic process. -/
noncomputable def rawMeasure : Measure Unit := Measure.dirac ()

noncomputable instance isProbabilityMeasure_rawMeasure :
    IsProbabilityMeasure rawMeasure := by
  unfold rawMeasure
  infer_instance

/-- The selected path, viewed as a process on the raw one-point space. -/
noncomputable def rawProcess : ℝ≥0 → Unit → ℝ :=
  fun t _ ↦ pathWitness.path t

theorem stronglyMeasurable_rawProcess (t : ℝ≥0) :
    StronglyMeasurable (rawProcess t) :=
  stronglyMeasurable_const

/-- The completed natural usual filtration of the deterministic process. -/
noncomputable def filtration :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace Unit rawMeasure)) :=
  (Filtration.natural rawProcess stronglyMeasurable_rawProcess).usualAugmentation rawMeasure

/-- The R36 process on the completed one-point probability space. -/
noncomputable def process :
    ℝ≥0 → NullMeasurableSpace Unit rawMeasure → ℝ :=
  fun t ω ↦ rawProcess t ω

theorem adapted_process : Adapted filtration process := by
  change Adapted
    ((Filtration.natural rawProcess stronglyMeasurable_rawProcess).usualAugmentation
      rawMeasure)
    (fun t (ω : NullMeasurableSpace Unit rawMeasure) ↦ rawProcess t ω)
  exact ((Filtration.stronglyAdapted_natural stronglyMeasurable_rawProcess).adapted
    |>.usualAugmentation rawMeasure)

theorem continuous_process (ω : NullMeasurableSpace Unit rawMeasure) :
    Continuous (fun t ↦ process t ω) := by
  simpa only [process, rawProcess] using pathWitness.continuous_path

theorem hasContinuousPaths_process :
    HasContinuousPaths process rawMeasure.completion :=
  ae_of_all _ continuous_process

/-- Every sample path has zero quadratic variation at horizon one along the
selected admissible deterministic partitions. -/
theorem zero_quadraticVariation_process
    (ω : NullMeasurableSpace Unit rawMeasure) :
    HasQuadraticVariationAlong
      (fun n ↦ (pathWitness.zeroPartition n).restrict 1)
      (fun t ↦ process t ω) 0 := by
  simpa only [process, rawProcess] using pathWitness.zero_quadraticVariation

/-- The same path has quadratic variation one along dyadic partitions.  This
is the incompatibility which rules out the semimartingale property. -/
theorem one_quadraticVariation_process
    (ω : NullMeasurableSpace Unit rawMeasure) :
    HasQuadraticVariationAlong
      (fun n ↦ (LocallyFinitePartition.dyadic n).restrict 1)
      (fun t ↦ process t ω) 1 := by
  simpa only [process, rawProcess] using pathWitness.one_quadraticVariation

private theorem tendstoInMeasure_sub_same
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {l : Filter ι} {f : ι → Ω → ℝ} {g c : Ω → ℝ}
    (h : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω ↦ f i ω - c ω) l (fun ω ↦ g ω - c ω) := by
  intro ε hε
  simpa only [edist_dist, dist_eq_norm, sub_sub_sub_cancel_right] using h ε hε

/-- Deterministic Klenke sums of a semimartingale converge in measure to its
canonical raw quadratic variation minus the initial square.  This is the
general-semimartingale form of the restriction argument used below. -/
private theorem semimartingale_tendstoInMeasure_quadraticVariationSum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    (T : ℝ≥0) :
    TendstoInMeasure P
      (fun n ω ↦ quadraticVariationSum ((π n).restrict T) (X · ω)) atTop
      (fun ω ↦ hX.quadraticVariation hF T ω - (X 0 ω) ^ 2) := by
  let ρ : ℕ → StoppingTimePartition F := fun n ↦
    StoppingTimePartition.deterministic F ((π n).restrict n)
  have hρ : StoppingTimePartition.IsTendingToIdentity ρ P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke hπ
      tendsto_natCast_atTop_atTop
  have hraw := (hX.tendstoUCP_quadraticVariationSumProcess hF hρ).fixedTime T
  have htranslated := tendstoInMeasure_sub_same
    (c := fun ω ↦ (X 0 ω) ^ 2) hraw
  refine TendstoInMeasure.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl) htranslated
  filter_upwards [
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop)
        |>.eventually (eventually_ge_atTop T)] with n hn
  exact ae_of_all P fun ω ↦ by
    change ((X 0 ω) ^ 2 + quadraticVariationSum ((π n).restrict n)
      (fun s ↦ X (min s T) ω)) - (X 0 ω) ^ 2 =
        quadraticVariationSum ((π n).restrict T) (X · ω)
    rw [(π n).quadraticVariationSum_restrict_eq_stop hn (X · ω)]
    ring

/-- The concrete continuous adapted zero-QV process is not a native
semimartingale. -/
theorem not_isSemimartingale_process :
    ¬ IsSemimartingale process filtration rawMeasure.completion := by
  intro hX
  have hF : filtration.IsUsual rawMeasure.completion := by
    simpa only [filtration] using
      (Filtration.natural rawProcess stronglyMeasurable_rawProcess
        |>.usualAugmentation_isUsual rawMeasure)
  have hcanonicalZero :=
    semimartingale_tendstoInMeasure_quadraticVariationSum hX hF
      pathWitness.zeroPartition_admissible 1
  have hpathZero :
      TendstoInMeasure rawMeasure.completion
        (fun n ω ↦ quadraticVariationSum
          ((pathWitness.zeroPartition n).restrict 1) (process · ω)) atTop
        (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ ↦ AEStronglyMeasurable.of_subsingleton_dom
    · exact ae_of_all _ zero_quadraticVariation_process
  have hcanonicalOne :=
    semimartingale_tendstoInMeasure_quadraticVariationSum hX hF
      LocallyFinitePartition.dyadic_admissible 1
  have hpathOne :
      TendstoInMeasure rawMeasure.completion
        (fun n ω ↦ quadraticVariationSum
          ((LocallyFinitePartition.dyadic n).restrict 1) (process · ω)) atTop
        (fun _ ↦ (1 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ ↦ AEStronglyMeasurable.of_subsingleton_dom
    · exact ae_of_all _ one_quadraticVariation_process
  have hzero := tendstoInMeasure_ae_unique hcanonicalZero hpathZero
  have hone := tendstoInMeasure_ae_unique hcanonicalOne hpathOne
  have hzeroOne :
      (fun _ : NullMeasurableSpace Unit rawMeasure ↦ (0 : ℝ))
        =ᵐ[rawMeasure.completion] fun _ ↦ (1 : ℝ) :=
    hzero.symm.trans hone
  obtain ⟨ω, hω⟩ := hzeroOne.exists
  norm_num at hω

/-- Packaged R36 statement: a named process is adapted, continuous on every
sample path, has pathwise zero QV along an admissible deterministic partition
sequence, and is nevertheless not a semimartingale. -/
theorem continuous_adapted_zeroQV_not_semimartingale :
    Adapted filtration process ∧
      (∀ ω, Continuous (fun t ↦ process t ω)) ∧
      IsAdmissiblePartitionSequence pathWitness.zeroPartition ∧
      (∀ ω, HasQuadraticVariationAlong
        (fun n ↦ (pathWitness.zeroPartition n).restrict 1)
        (fun t ↦ process t ω) 0) ∧
      ¬ IsSemimartingale process filtration rawMeasure.completion :=
  ⟨adapted_process, continuous_process, pathWitness.zeroPartition_admissible,
    zero_quadraticVariation_process, not_isSemimartingale_process⟩

end ProbabilityTheory.R36Counterexample
