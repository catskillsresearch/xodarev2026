/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.FutureEnvelope
public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilyConditional

/-! # Supermartingale order of actual future partition envelopes

Prepending the actual interval between two starting times makes every later
positive partition payoff a conditional lower bound of an earlier payoff.
The nonnegative first decrement and terminal-zero tail are both retained.
Directed essential-supremum comparison then proves the dynamic inequality.

All families and envelopes refer to the original measure. Arbitrary actual
envelope versions are compared to the previously constructed versions measurable
at the starting time. No dynamic inequality, cadlag version, or Rao decomposition
is assumed. This module does not assert cadlag regularity of the resulting process.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual whole-future positive envelopes satisfy supermartingale order.
Even the input versions need not themselves be measurable at the starting time:
their almost-sure equality to the constructed versions suffices. -/
theorem condExp_future_positive_partitionEnvelope_le
    (ha : Adapted F X) (hi : ∀ u, Integrable (X u) P)
    (hv : HasFiniteConditionalVariation X F P) {s t : ℝ≥0} (hst : s ≤ t) :
    let f : ℝ≥0 → (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ := fun u p ω ↦
      ENNReal.ofReal (P[(fun ω ↦
        (∑ i, max (P[X (u + p.2.left i) - X (u + p.2.right i) |
          F (u + p.2.left i)] ω) 0) + max (X (u + p.1) ω) 0) | F u] ω)
    ∀ {Ws Wt : Ω → ℝ≥0∞}, IsAEFamilySupremum P (f s) Ws →
      IsAEFamilySupremum P (f t) Wt →
      P[(fun ω ↦ (Wt ω).toReal) | F s] ≤ᵐ[P] (fun ω ↦ (Ws ω).toReal) := by
  classical
  dsimp only
  let f : ℝ≥0 → (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ := fun u p ω ↦
    ENNReal.ofReal (P[(fun ω ↦
      (∑ i, max (P[X (u + p.2.left i) - X (u + p.2.right i) |
        F (u + p.2.left i)] ω) 0) + max (X (u + p.1) ω) 0) | F u] ω)
  intro Ws Wt hWs hWt
  have hex (u : ℝ≥0) : ∃ V : Ω → ℝ≥0∞, Measurable[F u] V ∧
      IsAEFamilySupremum P (f u) V ∧ (∀ᵐ ω ∂P, V ω ≠ ∞) ∧
        Integrable (fun ω ↦ (V ω).toReal) P := by
    obtain ⟨V, Vn, hm, _, hV, _, _, _, hfin⟩ :=
      exists_future_positive_negative_partitionEnvelopes ha hi u
    obtain ⟨hff, hii, _⟩ := hfin hv
    refine ⟨V, hm, ?_, hff.mono (fun _ hω ↦ hω.1), hii⟩
    simpa only [f, Filtration.reindex_apply, add_zero] using hV
  obtain ⟨V, hmV, hV, hfV, hiV⟩ := hex s
  obtain ⟨U, _, hU, hfU, hiU⟩ := hex t
  have hfm (p : Σ H : ℝ≥0, TimePartition H) : Measurable (f t p) :=
    (stronglyMeasurable_condExp.measurable.ennreal_ofReal).mono (F.le t) le_rfl
  have hd : Directed (fun u v : Ω → ℝ≥0∞ ↦ u ≤ᵐ[P] v) (f t) := by
    let Y : ℝ≥0 → Ω → ℝ := fun u ↦ X (t + u)
    let G := F.reindex (fun u : ℝ≥0 ↦ t + u) (monotone_const.add monotone_id)
    have haY : Adapted G Y := fun u ↦ ha (t + u)
    have hiY (u : ℝ≥0) : Integrable (Y u) P := hi (t + u)
    simpa only [f, Y, G, Filtration.reindex_apply, add_zero] using
      directed_positive_conditional_decrements_all_horizons haY hiY
  have hb (p : Σ H : ℝ≥0, TimePartition H) :
      P[(fun ω ↦ (f t p ω).toReal) | F s] ≤ᵐ[P] (fun ω ↦ (V ω).toReal) := by
    obtain ⟨ρ, _, hsum⟩ := p.2.exists_prepend_shift (t - s)
    let q : Σ H : ℝ≥0, TimePartition H := ⟨(t - s) + p.1, ρ⟩
    let B : Ω → ℝ := fun ω ↦
      (∑ i, max (P[X (t + p.2.left i) - X (t + p.2.right i) |
        F (t + p.2.left i)] ω) 0) + max (X (t + p.1) ω) 0
    let C : Ω → ℝ := fun ω ↦
      (∑ i, max (P[X (s + ρ.left i) - X (s + ρ.right i) |
        F (s + ρ.left i)] ω) 0) + max (X (s + ((t - s) + p.1)) ω) 0
    have hiB : Integrable B P :=
      (integrable_finsetSum Finset.univ (fun i _ ↦
        (integrable_condExp (f := X (t + p.2.left i) - X (t + p.2.right i))
          (m := F (t + p.2.left i))).sup (integrable_zero _ _ _))).add
        ((hi (t + p.1)).sup (integrable_zero _ _ _))
    have hiC : Integrable C P :=
      (integrable_finsetSum Finset.univ (fun i _ ↦
        (integrable_condExp (f := X (s + ρ.left i) - X (s + ρ.right i))
          (m := F (s + ρ.left i))).sup (integrable_zero _ _ _))).add
        ((hi (s + ((t - s) + p.1))).sup (integrable_zero _ _ _))
    have hBn (ω : Ω) : 0 ≤ B ω :=
      add_nonneg (sum_nonneg fun _ _ ↦ le_max_right _ _) (le_max_right _ _)
    have hCn (ω : Ω) : 0 ≤ C ω :=
      add_nonneg (sum_nonneg fun _ _ ↦ le_max_right _ _) (le_max_right _ _)
    have hBC : B ≤ᵐ[P] C := by
      apply Eventually.of_forall
      intro ω
      have he : C ω = max (P[X s - X t | F s] ω) 0 + B ω := by
        dsimp only [C, B]
        rw [hsum (fun a b ↦ max (P[X (s + a) - X (s + b) | F (s + a)] ω) 0)]
        simp only [add_zero, ← add_assoc, add_tsub_cancel_of_le hst]
      rw [he]
      exact le_add_of_nonneg_left (le_max_right _ _)
    have heB : (fun ω ↦ (f t p ω).toReal) =ᵐ[P] P[B | F t] := by
      filter_upwards [condExp_nonneg (m := F t) (Eventually.of_forall hBn)] with ω hω
      exact ENNReal.toReal_ofReal hω
    have heC : (fun ω ↦ (f s q ω).toReal) =ᵐ[P] P[C | F s] := by
      filter_upwards [condExp_nonneg (m := F s) (Eventually.of_forall hCn)] with ω hω
      exact ENNReal.toReal_ofReal hω
    have hle : P[(fun ω ↦ (f t p ω).toReal) | F s] ≤ᵐ[P]
        (fun ω ↦ (f s q ω).toReal) := by
      filter_upwards [condExp_congr_ae (m := F s) heB,
        condExp_condExp_of_le (f := B) (F.mono hst) (F.le t),
        condExp_mono hiB hiC hBC, heC] with ω hBω htω hmω hCω
      rw [hBω, htω, hCω]
      exact hmω
    have hq : (fun ω ↦ (f s q ω).toReal) ≤ᵐ[P] (fun ω ↦ (V ω).toReal) := by
      filter_upwards [hV.le_ae q, hfV] with ω hω hfω
      exact ENNReal.toReal_mono hfω hω
    exact hle.trans hq
  have hUV : P[(fun ω ↦ (U ω).toReal) | F s] ≤ᵐ[P]
      (fun ω ↦ (V ω).toReal) :=
    hU.condExp_toReal_le_of_ae_directed hfm hd hfU hiU (F.le s)
      hmV.ennreal_toReal.stronglyMeasurable hiV
      (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hb
  have heU := condExp_congr_ae (m := F s) ((hWt.ae_eq hU).fun_comp ENNReal.toReal)
  have heV := (hWs.ae_eq hV).fun_comp ENNReal.toReal
  filter_upwards [heU, hUV, heV] with ω huω huvω hvω
  exact huω.trans_le (huvω.trans_eq hvω.symm)

/-- Any starting-time-measurable selection of the actual positive future
envelopes is a genuine nonnegative supermartingale after safe real conversion.
The coordinate integrability and conditional order are derived, not assumed. -/
theorem supermartingale_future_positive_partitionEnvelopes
    (ha : Adapted F X) (hi : ∀ u, Integrable (X u) P)
    (hv : HasFiniteConditionalVariation X F P) :
    let f : ℝ≥0 → (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ := fun u p ω ↦
      ENNReal.ofReal (P[(fun ω ↦
        (∑ i, max (P[X (u + p.2.left i) - X (u + p.2.right i) |
          F (u + p.2.left i)] ω) 0) + max (X (u + p.1) ω) 0) | F u] ω)
    ∀ {W : ℝ≥0 → Ω → ℝ≥0∞}, (∀ u, Measurable[F u] (W u)) →
      (∀ u, IsAEFamilySupremum P (f u) (W u)) →
      Supermartingale (fun u ω ↦ (W u ω).toReal) F P := by
  dsimp only
  intro W hm hW
  refine ⟨fun u ↦ (hm u).ennreal_toReal.stronglyMeasurable,
    fun s t hst ↦ condExp_future_positive_partitionEnvelope_le ha hi hv hst (hW s) (hW t),
    fun u ↦ ?_⟩
  obtain ⟨V, Vn, _, _, hV, _, _, _, hfin⟩ :=
    exists_future_positive_negative_partitionEnvelopes ha hi u
  obtain ⟨_, hiV, _⟩ := hfin hv
  have he : W u =ᵐ[P] V := by
    apply (hW u).ae_eq
    simpa only [Filtration.reindex_apply, add_zero] using hV
  exact hiV.congr (he.symm.fun_comp ENNReal.toReal)

end ProbabilityTheory
