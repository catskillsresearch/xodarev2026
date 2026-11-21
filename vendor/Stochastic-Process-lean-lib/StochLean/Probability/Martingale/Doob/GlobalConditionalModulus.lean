/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulus

/-! # Conditional increment moduli on the whole half-line

The global index includes every ordered pair of finite times with the specified window width.
The modulus is still the existing measurable essential-family-supremum relation, not a raw
uncountable supremum of unrelated representatives. Compact moduli are below global moduli.

If the process is constant after a deterministic time `T` on one common full-measure event,
the global modulus equals the compact modulus with horizon `T`. For a starting time at most
`T`, the ending time is clipped to `T`; after `T`, the increment is zero. This deterministic
bridge does not claim the source theorem with a random terminal time.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- All ordered finite-time pairs within a fixed nonnegative window width. -/
abbrev GlobalConditionalIncrementIndex (δ : ℝ≥0) :=
  {p : ℝ≥0 × ℝ≥0 // p.1 ≤ p.2 ∧ p.2 ≤ p.1 + δ}

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def globalConditionalIncrementFamily (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0)
    (i : GlobalConditionalIncrementIndex δ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (P[X i.1.1 - X i.1.2 | F i.1.1] ω)

/-- A global conditional modulus is a measurable essential upper bound of all short increments. -/
abbrev IsGlobalConditionalIncrementModulus (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0) (W : Ω → ℝ≥0∞) : Prop :=
  IsAEFamilySupremum P (globalConditionalIncrementFamily F P X δ) W

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {T δ η : ℝ≥0} {W V : Ω → ℝ≥0∞}

theorem measurable_globalConditionalIncrementFamily (i : GlobalConditionalIncrementIndex δ) :
    Measurable (globalConditionalIncrementFamily F P X δ i) :=
  ENNReal.measurable_ofReal.comp
    (stronglyMeasurable_condExp.measurable.mono (F.le i.1.1) le_rfl)

theorem exists_globalConditionalIncrementModulus
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [SFinite P]
    (X : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0) :
    ∃ W : Ω → ℝ≥0∞, IsGlobalConditionalIncrementModulus F P X δ W :=
  exists_isAEFamilySupremum P (fun i ↦ measurable_globalConditionalIncrementFamily i)

theorem IsGlobalConditionalIncrementModulus.ae_eq
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    (hV : IsGlobalConditionalIncrementModulus F P X δ V) : W =ᵐ[P] V :=
  IsAEFamilySupremum.ae_eq hW hV

theorem IsGlobalConditionalIncrementModulus.conditional_increment_le
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    {t u : ℝ≥0} (htu : t ≤ u) (huδ : u ≤ t + δ) :
    (fun ω ↦ ENNReal.ofReal (P[X t - X u | F t] ω)) ≤ᵐ[P] W :=
  hW.le_ae ⟨(t, u), htu, huδ⟩

theorem IsGlobalConditionalIncrementModulus.ae_le_of_bound
    (hW : IsGlobalConditionalIncrementModulus F P X δ W) (U : Ω → ℝ≥0∞)
    (hU : ∀ t u : ℝ≥0, t ≤ u → u ≤ t + δ →
      (fun ω ↦ ENNReal.ofReal (P[X t - X u | F t] ω)) ≤ᵐ[P] U) : W ≤ᵐ[P] U :=
  hW.ae_le U (fun i ↦ hU i.1.1 i.1.2 i.2.1 i.2.2)

theorem IsConditionalIncrementModulus.ae_le_global
    (hV : IsConditionalIncrementModulus F P X T δ V)
    (hW : IsGlobalConditionalIncrementModulus F P X δ W) : V ≤ᵐ[P] W := by
  apply hV.ae_le_of_bound W
  intro t u htu _ huδ
  exact hW.conditional_increment_le htu huδ

theorem IsGlobalConditionalIncrementModulus.mono_width
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    (hV : IsGlobalConditionalIncrementModulus F P X η V) (hδη : δ ≤ η) : W ≤ᵐ[P] V := by
  apply hW.ae_le_of_bound V
  intro t u htu huδ
  exact hV.conditional_increment_le htu (huδ.trans (add_le_add le_rfl hδη))

theorem isGlobalConditionalIncrementModulus_zero_width (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) :
    IsGlobalConditionalIncrementModulus F P X 0 (fun _ ↦ 0) := by
  have hz (i : GlobalConditionalIncrementIndex 0) :
      globalConditionalIncrementFamily F P X 0 i = 0 := by
    have he : i.1.1 = i.1.2 := le_antisymm i.2.1 (by simpa only [add_zero] using i.2.2)
    funext ω
    simp only [globalConditionalIncrementFamily, he, sub_self, condExp_zero,
      Pi.zero_apply, ENNReal.ofReal_zero]
  refine ⟨measurable_const, fun i ↦ ?_, fun _ _ ↦ Eventually.of_forall fun _ ↦ bot_le⟩
  rw [hz]
  exact Eventually.of_forall fun _ ↦ le_rfl

theorem IsGlobalConditionalIncrementModulus.ae_eq_zero_of_zero_width
    (hW : IsGlobalConditionalIncrementModulus F P X 0 W) : W =ᵐ[P] (fun _ ↦ 0) :=
  hW.ae_eq (isGlobalConditionalIncrementModulus_zero_width F P X)

theorem IsGlobalConditionalIncrementModulus.ae_le_of_norm_bound [IsFiniteMeasure P]
    (hW : IsGlobalConditionalIncrementModulus F P X δ W) {N : ℝ}
    (hi : ∀ t, Integrable (X t) P) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    W ≤ᵐ[P] (fun _ ↦ ENNReal.ofReal (2 * N)) := by
  apply hW.ae_le_of_bound
  intro t u _ _
  have hdiff : X t - X u ≤ᵐ[P] (fun _ ↦ 2 * N) := by
    filter_upwards [hb t, hb u] with ω ht hu
    have hnorm := (norm_sub_le (X t ω) (X u ω)).trans (add_le_add ht hu)
    have hs : X t ω - X u ω ≤ ‖X t ω - X u ω‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (X t ω - X u ω)
    change X t ω - X u ω ≤ 2 * N
    linarith
  have hce := condExp_mono (m := F t) ((hi t).sub (hi u))
    (integrable_const (2 * N)) hdiff
  rw [condExp_const (F.le t)] at hce
  exact hce.mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω

theorem IsGlobalConditionalIncrementModulus.ae_ne_top_of_norm_bound [IsFiniteMeasure P]
    (hW : IsGlobalConditionalIncrementModulus F P X δ W) {N : ℝ}
    (hi : ∀ t, Integrable (X t) P) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    ∀ᵐ ω ∂P, W ω ≠ ∞ :=
  (hW.ae_le_of_norm_bound hi hb).mono fun _ hω ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω

/-- If all paths are constant after deterministic `T` on a common full-measure event, the
global modulus is bounded by the compact one. Comparisons are made for each fixed pair before
using essential-supremum minimality, with no uncountable intersection of null events. -/
theorem IsGlobalConditionalIncrementModulus.ae_le_compact_of_deterministic_stop
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    (hV : IsConditionalIncrementModulus F P X T δ V)
    (hstop : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = X (min t T) ω) : W ≤ᵐ[P] V := by
  apply hW.ae_le_of_bound V
  intro t u htu huδ
  by_cases htT : t ≤ T
  · have htv : t ≤ min u T := le_min htu htT
    have hdiff : X t - X u =ᵐ[P] X t - X (min u T) := by
      filter_upwards [hstop] with ω hω
      change X t ω - X u ω = X t ω - X (min u T) ω
      rw [hω u]
    have hce := condExp_congr_ae (m := F t) hdiff
    have hbound := hV.conditional_increment_le htv (min_le_right u T)
      ((min_le_left u T).trans huδ)
    filter_upwards [hce, hbound] with ω he hle
    exact (congrArg ENNReal.ofReal he).trans_le hle
  · have hTt : T ≤ t := (lt_of_not_ge htT).le
    have hTu : T ≤ u := hTt.trans htu
    have hdiff : X t - X u =ᵐ[P] (fun _ ↦ 0) := by
      filter_upwards [hstop] with ω hω
      change X t ω - X u ω = 0
      rw [hω t, hω u, min_eq_right hTt, min_eq_right hTu, sub_self]
    have hz : P[X t - X u | F t] =ᵐ[P] (fun _ ↦ 0) := by
      have hzero := condExp_congr_ae (m := F t) (g := (0 : Ω → ℝ)) hdiff
      rw [condExp_zero] at hzero
      filter_upwards [hzero] with ω hω
      simpa only [Pi.zero_apply] using hω
    filter_upwards [hz] with ω hω
    rw [hω, ENNReal.ofReal_zero]
    exact bot_le

/-- Deterministically terminated paths have the same global and compact conditional modulus.
The terminal time here is deterministic; no random-lifetime reduction is asserted. -/
theorem IsGlobalConditionalIncrementModulus.ae_eq_compact_of_deterministic_stop
    (hW : IsGlobalConditionalIncrementModulus F P X δ W)
    (hV : IsConditionalIncrementModulus F P X T δ V)
    (hstop : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = X (min t T) ω) : W =ᵐ[P] V := by
  filter_upwards [hW.ae_le_compact_of_deterministic_stop hV hstop,
    hV.ae_le_global hW] with ω hw hv
  exact le_antisymm hw hv

end ProbabilityTheory
