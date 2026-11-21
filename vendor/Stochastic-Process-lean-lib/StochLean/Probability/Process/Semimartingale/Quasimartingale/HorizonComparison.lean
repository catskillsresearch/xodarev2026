/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.HorizonExtension
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.PartitionEnvelope

/-! # Conditional variation across finite horizons

Extending a horizon replaces the old terminal-zero tail by one conditional
decrement and the new terminal-zero tail. Adaptedness is essential here: the
old terminal value must equal its conditional expectation at its own time.
This gives actual directedness over all finite horizons after conditioning.

Prepending `[0,t]` to a shifted partition bounds its actual conditional
variation by the original whole-half-line owner. This latter pathwise sum
comparison needs neither adaptedness nor an integrability premise.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H K : ℝ≥0}

/-- The positive terminal-zero tail is controlled by its new final
conditional decrement and the new terminal-zero tail after conditioning. -/
theorem condExp_positive_terminal_tail_le (ha : Adapted F X)
    (hi : ∀ t, Integrable (X t) P) (_hHK : H ≤ K) :
    P[(fun ω ↦ max (X H ω) 0) | F 0] ≤ᵐ[P]
      P[(fun ω ↦ max (P[X H - X K | F H] ω) 0 + max (X K ω) 0) | F 0] := by
  let B : Ω → ℝ := fun ω ↦ max (P[X H - X K | F H] ω) 0
  let C : Ω → ℝ := fun ω ↦ max (X K ω) 0
  have hB : Integrable B P := integrable_condExp.sup (integrable_zero _ _ _)
  have hC : Integrable C P := (hi K).sup (integrable_zero _ _ _)
  have he : P[X H - X K | F H] =ᵐ[P] X H - P[X K | F H] := by
    simpa only [condExp_of_stronglyMeasurable (F.le H) (ha.stronglyAdapted H) (hi H)]
      using condExp_sub (hi H) (hi K) (F H)
  have hm : P[X K | F H] ≤ᵐ[P] P[C | F H] :=
    condExp_mono (hi K) hC (Eventually.of_forall fun ω ↦ le_max_left (X K ω) 0)
  have hn : 0 ≤ᵐ[P] P[C | F H] :=
    condExp_nonneg (Eventually.of_forall fun ω ↦ le_max_right (X K ω) 0)
  have hinner : (fun ω ↦ max (X H ω) 0) ≤ᵐ[P] B + P[C | F H] := by
    filter_upwards [he, hm, hn] with ω heω hmω hnω
    simp only [Pi.sub_apply] at heω
    change max (X H ω) 0 ≤ B ω + P[C | F H] ω
    apply max_le
    · have hmax := le_max_left (P[X H - X K | F H] ω) 0
      change _ ≤ B ω at hmax
      linarith only [heω, hmω, hmax]
    · exact add_nonneg (le_max_right _ _) hnω
  have ho := condExp_mono (m := F 0) (f := fun ω ↦ max (X H ω) 0)
    ((hi H).sup (integrable_zero _ _ _))
    (hB.add integrable_condExp) hinner
  have hleft := condExp_add hB (integrable_condExp (f := C) (m := F H)) (F 0)
  have hright := condExp_add hB hC (F 0)
  have ht := condExp_condExp_of_le (μ := P) (F.mono (show 0 ≤ H from bot_le)) (F.le H)
    (f := C)
  have hres : P[(fun ω ↦ max (X H ω) 0) | F 0] ≤ᵐ[P] P[B + C | F 0] := by
    filter_upwards [ho, hleft, hright, ht] with ω hoω hlω hrω htω
    simpa only [hlω, hrω, Pi.add_apply, htω] using hoω
  simpa only [B, C, Pi.add_def] using hres

/-- A larger terminal horizon admits an actual extended partition whose
positive conditional-decrement family member dominates the old one. -/
theorem exists_positive_conditional_decrements_extension (ha : Adapted F X)
    (hi : ∀ t, Integrable (X t) P) (π : TimePartition H) (hHK : H ≤ K) :
    ∃ ρ : TimePartition K, Set.range ρ.point = Set.range π.point ∪ {K} ∧
      P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
        max (X H ω) 0) | F 0] ≤ᵐ[P]
      P[(fun ω ↦ (∑ j, max (P[X (ρ.left j) - X (ρ.right j) | F (ρ.left j)] ω) 0) +
        max (X K ω) 0) | F 0] := by
  obtain ⟨ρ, hρ, hsum⟩ := π.exists_extend_horizon hHK
  let B : Ω → ℝ := fun ω ↦
    ∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0
  let C : Ω → ℝ := fun ω ↦ max (X H ω) 0
  let D : Ω → ℝ := fun ω ↦ max (P[X H - X K | F H] ω) 0 + max (X K ω) 0
  have hB : Integrable B P := integrable_finsetSum Finset.univ (fun i _ ↦
    (integrable_condExp (f := X (π.left i) - X (π.right i)) (m := F (π.left i))).sup
      (integrable_zero _ _ _))
  have hC : Integrable C P := (hi H).sup (integrable_zero _ _ _)
  have hD : Integrable D P :=
    (integrable_condExp.sup (integrable_zero _ _ _)).add
      ((hi K).sup (integrable_zero _ _ _))
  have htail : P[C | F 0] ≤ᵐ[P] P[D | F 0] := condExp_positive_terminal_tail_le ha hi hHK
  have hle : P[B + C | F 0] ≤ᵐ[P] P[B + D | F 0] := by
    filter_upwards [condExp_add hB hC (F 0), condExp_add hB hD (F 0), htail]
      with ω hcω hdω htω
    simp only [hcω, hdω, Pi.add_apply]
    exact add_le_add (le_refl _) htω
  refine ⟨ρ, hρ, ?_⟩
  have hnew : (fun ω ↦
      (∑ j, max (P[X (ρ.left j) - X (ρ.right j) | F (ρ.left j)] ω) 0) + max (X K ω) 0) =
      B + D := by
    funext ω
    rw [hsum (fun s u ↦ max (P[X s - X u | F s] ω) 0)]
    simp only [B, D, Pi.add_apply, add_assoc]
  rw [hnew]
  simpa only [B, C, Pi.add_def] using hle

/-- Positive conditional partition decrements are genuinely directed over
all finite horizons, not merely over partitions of one fixed interval. -/
theorem directed_positive_conditional_decrements_all_horizons
    (ha : Adapted F X) (hi : ∀ t, Integrable (X t) P) :
    Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v)
      (fun p : Σ H : ℝ≥0, TimePartition H ↦ fun ω ↦ ENNReal.ofReal
        (P[(fun ω ↦
          (∑ i, max (P[X (p.2.left i) - X (p.2.right i) | F (p.2.left i)] ω) 0) +
            max (X p.1 ω) 0) | F 0] ω)) := by
  intro p q
  obtain ⟨ρ, _, hρ⟩ := exists_positive_conditional_decrements_extension ha hi p.2
    (le_max_left p.1 q.1)
  obtain ⟨σ, _, hσ⟩ := exists_positive_conditional_decrements_extension ha hi q.2
    (le_max_right p.1 q.1)
  refine ⟨⟨max p.1 q.1, ρ.commonRefinement σ⟩, ?_, ?_⟩
  · exact (hρ.trans (condExp_positive_conditional_decrements_le_of_refines hi
      (ρ.commonRefinement_refines_left σ))).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω
  · exact (hσ.trans (condExp_positive_conditional_decrements_le_of_refines hi
      (ρ.commonRefinement_refines_right σ))).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω

omit [IsFiniteMeasure P] in
/-- Prepending the missing initial interval bounds the actual conditional
variation of a deterministic time shift by the original global owner. -/
theorem eConditionalVariation_shift_le (t : ℝ≥0) :
    eConditionalVariation (fun s ↦ X (t + s))
      (F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)) P ≤
      eConditionalVariation X F P := by
  let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
  let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
  apply iSup_le
  intro H
  apply iSup_le
  intro π
  obtain ⟨ρ, _, hsum⟩ := π.exists_prepend_shift t
  apply le_trans ?_ (eConditionalVariationOnPartition_le (X := X) (F := F) (P := P) ρ)
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  have he : conditionalVariationSum X F P ρ ω =
      |P[X 0 - X t | F 0] ω| + conditionalVariationSum Y G P π ω := by
    unfold conditionalVariationSum
    rw [hsum (fun s u ↦ |P[X s - X u | F s] ω|)]
    change |P[X 0 - X t | F 0] ω| +
        (∑ i, |P[X (t + π.left i) - X (t + π.right i) | F (t + π.left i)] ω|) +
          |X (t + H) ω - 0| =
      |P[X 0 - X t | F 0] ω| +
        ((∑ i, |P[X (t + π.left i) - X (t + π.right i) | F (t + π.left i)] ω|) +
          |X (t + H) ω - 0|)
    ring
  rw [he]
  exact le_add_of_nonneg_left (abs_nonneg _)

end ProbabilityTheory
