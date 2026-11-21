/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Brownian.QuadraticVariationConditional
import StochLean.Probability.Martingale.Reverse
import StochLean.Probability.Process.Filtration.Future
import StochLean.Analysis.PathVariation.AdmissiblePartition

/-! # Strong Brownian quadratic variation on nested partitions

The square sums are actual conditional expectations of `B_T²` in their decreasing future
sigma-fields. Lévy's downward theorem yields almost-sure convergence; the existing variance
estimate identifies its limit. There is no summability assumption on the mesh.
-/

open MeasureTheory Filter StochLean
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem IsPreBrownianReal.condExp_terminal_sq_future_quadraticVariationSum
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (π : ℕ → TimePartition T) (hnest : ∀ n m, n ≤ m → (π m).Refines (π n)) (n : ℕ) :
    P[(fun ω ↦ (B T ω) ^ 2) |
      futureMeasurableSpace (fun k ω ↦ quadraticVariationSum (π k) (B · ω)) n] =ᵐ[P]
      fun ω ↦ quadraticVariationSum (π n) (B · ω) := by
  rw [futureMeasurableSpace_nat_eq_comap]
  exact hB.condExp_terminal_sq_eq_quadraticVariationSum hBm (π n) (fun k ↦ π (n + k))
    (fun k ↦ hnest n (n + k) (Nat.le_add_right n k)) (by simp)

/-- The source reverse martingale consists of the actual square sums, not a hypothesized
auxiliary sequence. Its adaptedness is for the canonical future sigma-fields. -/
theorem IsPreBrownianReal.reverseMartingale_quadraticVariationSum
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (π : ℕ → TimePartition T) (hnest : ∀ n m, n ≤ m → (π m).Refines (π n)) :
    let Q := fun k ω ↦ quadraticVariationSum (π k) (B · ω)
    ReverseMartingale (fun n : OrderDual ℕ ↦ Q n) (futureMeasurableSpace Q)
      (futureMeasurableSpace_antitone Q)
      (fun n ↦ futureMeasurableSpace_le Q n mΩ (fun k _ ↦
        (measurable_quadraticVariationSum (π k)).comp (measurable_pi_lambda _ hBm))) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  dsimp only
  apply (reverseMartingale_condExp (fun ω ↦ (B T ω) ^ 2) _ _ _ P).congr
  · intro n
    exact (measurable_futureMeasurableSpace
      (fun k ω ↦ quadraticVariationSum (π k) (B · ω)) n).stronglyMeasurable
  · exact fun n ↦ hB.condExp_terminal_sq_future_quadraticVariationSum hBm π hnest n

/-- Protter I.28 / Klenke 21.64 at a fixed horizon, with arbitrary nested vanishing mesh. -/
theorem IsPreBrownianReal.ae_quadraticVariationAlong_of_nested_mesh_of_measurable
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {π : ℕ → TimePartition T} (hnest : ∀ n m, n ≤ m → (π m).Refines (π n))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, HasQuadraticVariationAlong π (B · ω) T := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let Q := fun k ω ↦ quadraticVariationSum (π k) (B · ω)
  let G := futureMeasurableSpace Q
  have hGle (n : ℕ) : G n ≤ mΩ :=
    futureMeasurableSpace_le Q n mΩ (fun k _ ↦
      (measurable_quadraticVariationSum (π k)).comp (measurable_pi_lambda _ hBm))
  have hBT : Integrable (fun ω ↦ (B T ω) ^ 2) P :=
    ((hB.hasLaw_eval T).hasGaussianLaw.memLp_two).integrable_sq
  have hce := tendsto_ae_condExp_iInf (futureMeasurableSpace_antitone Q) hGle
    (fun ω ↦ (B T ω) ^ 2) hBT
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Q n ω) atTop
      (𝓝 (P[(fun ω ↦ (B T ω) ^ 2) | ⨅ n, G n] ω)) := by
    filter_upwards [hce, ae_all_iff.mpr
      (hB.condExp_terminal_sq_future_quadraticVariationSum hBm π hnest)] with ω hω heq
    exact hω.congr' (Eventually.of_forall heq)
  have hid := tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (hB.memLp_quadraticVariationSum (π n)).aestronglyMeasurable) hlim)
    (hB.tendstoInMeasure_quadraticVariationSum hmesh)
  filter_upwards [hlim, hid] with ω hω heq
  exact heq ▸ hω

/-- Coordinatewise measurable versions suffice at a fixed horizon: the union of all partition
endpoints is countable. No uncountable intersection of coordinate null events is taken. -/
theorem IsPreBrownianReal.ae_quadraticVariationAlong_of_nested_mesh
    (hB : IsPreBrownianReal B P) {π : ℕ → TimePartition T}
    (hnest : ∀ n m, n ≤ m → (π m).Refines (π n))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, HasQuadraticVariationAlong π (B · ω) T := by
  let C : ℝ≥0 → Ω → ℝ := fun t ↦ (hB.aemeasurable t).mk (B t)
  have heq (t : ℝ≥0) : B t =ᵐ[P] C t := (hB.aemeasurable t).ae_eq_mk
  have hC := hB.congr heq
  have hlim := hC.ae_quadraticVariationAlong_of_nested_mesh_of_measurable
    (fun t ↦ (hB.aemeasurable t).measurable_mk) hnest hmesh
  have hsums (n : ℕ) : (fun ω ↦ quadraticVariationSum (π n) (B · ω)) =ᵐ[P]
      fun ω ↦ quadraticVariationSum (π n) (C · ω) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin ((π n).size + 1) ↦ heq ((π n).point i))]
      with ω hω
    unfold quadraticVariationSum TimePartition.increment TimePartition.left TimePartition.right
    simp only [hω]
  filter_upwards [hlim, ae_all_iff.mpr hsums] with ω hω hsum
  exact hω.congr' (Eventually.of_forall (fun n ↦ (hsum n).symm))

/-- The arbitrary nested finite-partition theorem applies to the lossless restrictions of the
source's locally finite infinite partitions. The corrected adjacent-gap mesh is the only rate. -/
theorem IsPreBrownianReal.ae_quadraticVariationAlong_restrict
    (hB : IsPreBrownianReal B P) {π : ℕ → LocallyFinitePartition}
    (hπ : IsAdmissiblePartitionSequence π) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) (B · ω) T := by
  apply hB.ae_quadraticVariationAlong_of_nested_mesh
  · intro n m hnm t ht
    apply ((π m).mem_range_restrict T t).mpr
    rcases ((π n).mem_range_restrict T t).mp ht with ht | ⟨ht, htT⟩
    · exact Or.inl ht
    · exact Or.inr ⟨hπ.1 hnm ht, htT⟩
  · simpa only [Function.comp_def, NNReal.coe_zero] using
      NNReal.continuous_coe.continuousAt.tendsto.comp (hπ.restrict_mesh_tendsto (fun _ ↦ T))

end ProbabilityTheory
