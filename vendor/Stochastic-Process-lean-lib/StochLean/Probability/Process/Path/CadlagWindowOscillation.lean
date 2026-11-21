/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagShortWindow
public import StochLean.Probability.Process.Path.Supremum

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Absolute increments on ordered pairs of clipped dense times less than the
given width apart. This is an extended nonnegative supremum, not a maximum. -/
noncomputable def denseWindowOscillation (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ,
    if denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
        denseTimeUpTo T j < denseTimeUpTo T i + δ then
      ENNReal.ofReal ‖X (denseTimeUpTo T j) ω - X (denseTimeUpTo T i) ω‖ else 0

theorem measurable_denseWindowOscillation {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T δ : ℝ≥0) :
    Measurable (denseWindowOscillation X T δ) := by
  apply Measurable.iSup
  intro i
  apply Measurable.iSup
  intro j
  by_cases h : denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
      denseTimeUpTo T j < denseTimeUpTo T i + δ
  · simp only [if_pos h]
    exact ENNReal.measurable_ofReal.comp ((hX _).sub (hX _)).norm
  · simp only [if_neg h]
    exact measurable_const

@[simp] theorem denseWindowOscillation_zero (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    denseWindowOscillation X T 0 ω = 0 := by
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  have hn : ¬ (denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
      denseTimeUpTo T j < denseTimeUpTo T i + 0) := by
    simpa only [add_zero, not_and, not_lt] using
      (fun h : denseTimeUpTo T i ≤ denseTimeUpTo T j ↦ h)
  rw [if_neg hn]
  exact le_rfl

theorem denseWindowOscillation_mono_width (X : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {δ η : ℝ≥0} (hδη : δ ≤ η) (ω : Ω) :
    denseWindowOscillation X T δ ω ≤ denseWindowOscillation X T η ω := by
  apply iSup_mono
  intro i
  apply iSup_mono
  intro j
  by_cases h : denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
      denseTimeUpTo T j < denseTimeUpTo T i + δ
  · have hsum : denseTimeUpTo T i + δ ≤ denseTimeUpTo T i + η := by gcongr
    have h' := And.intro h.1 (h.2.trans_le hsum)
    simp only [if_pos h, if_pos h', le_refl]
  · rw [if_neg h]
    exact bot_le

theorem ofReal_norm_sub_le_denseWindowOscillation_grid {X : ℝ≥0 → Ω → ℝ}
    {T δ : ℝ≥0} {i j : ℕ} (hij : denseTimeUpTo T i ≤ denseTimeUpTo T j)
    (hwidth : denseTimeUpTo T j < denseTimeUpTo T i + δ) (ω : Ω) :
    ENNReal.ofReal ‖X (denseTimeUpTo T j) ω - X (denseTimeUpTo T i) ω‖ ≤
      denseWindowOscillation X T δ ω := by
  apply le_iSup_of_le i
  apply le_iSup_of_le j
  have hguard : denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
      denseTimeUpTo T j < denseTimeUpTo T i + δ := ⟨hij, hwidth⟩
  rw [if_pos hguard]

theorem denseWindowOscillation_le_of_bound {X : ℝ≥0 → Ω → ℝ}
    {T δ : ℝ≥0} {ω : Ω} {K : ℝ}
    (hK : ∀ r s : ℝ≥0, r ≤ s → s ≤ T → s < r + δ → ‖X s ω - X r ω‖ ≤ K) :
    denseWindowOscillation X T δ ω ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  by_cases h : denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
      denseTimeUpTo T j < denseTimeUpTo T i + δ
  · rw [if_pos h]
    exact ENNReal.ofReal_le_ofReal (hK _ _ h.1 (min_le_left _ _) h.2)
  · rw [if_neg h]
    exact bot_le

theorem denseWindowOscillation_ne_top_of_cadlag {X : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hX : IsCadlagPath (X · ω)) (T δ : ℝ≥0) :
    denseWindowOscillation X T δ ω ≠ ∞ := by
  obtain ⟨K, _, hK⟩ := hX.exists_norm_bound_Icc T
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply denseWindowOscillation_le_of_bound (K := 2 * K)
  intro r s hrs hsT _
  have hr := hK r ⟨bot_le, hrs.trans hsT⟩
  have hs := hK s ⟨bot_le, hsT⟩
  have htri := norm_sub_le (X s ω) (X r ω)
  linarith only [htri, hr, hs]

private theorem exists_denseTimeUpTo_right_approximation {T t : ℝ≥0} (ht : t ≤ T) :
    ∃ u : ℕ → ℕ, Tendsto (fun n ↦ denseTimeUpTo T (u n)) atTop (𝓝[≥] t) := by
  have hdense : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨v, _, hv, hlim⟩ := hdense.exists_seq_strictAnti_tendsto t
  choose u hu using fun n ↦ (hv n).2
  have he (n : ℕ) : denseTimeUpTo T (u n) = min T (v n) := by
    rw [denseTimeUpTo, hu n]
  refine ⟨u, tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩⟩
  · simpa only [he, min_eq_right ht] using
      ((show Tendsto (fun _ : ℕ ↦ T) atTop (𝓝 T) from tendsto_const_nhds).min hlim)
  · exact Eventually.of_forall fun n ↦ by
      rw [he]
      exact le_min ht (hv n).1.le

theorem ofReal_norm_sub_le_denseWindowOscillation_of_rightContinuous
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {T δ r s : ℝ≥0} (hrs : r ≤ s) (hsT : s ≤ T) (hwidth : s < r + δ) :
    ENNReal.ofReal ‖X s ω - X r ω‖ ≤ denseWindowOscillation X T δ ω := by
  rcases hrs.eq_or_lt with he | hrs
  · subst s
    simp only [sub_self, norm_zero, ENNReal.ofReal_zero, zero_le]
  obtain ⟨u, hu⟩ := exists_denseTimeUpTo_right_approximation (hrs.le.trans hsT)
  obtain ⟨v, hv⟩ := exists_denseTimeUpTo_right_approximation hsT
  have hut := hu.mono_right nhdsWithin_le_nhds
  have hvt := hv.mono_right nhdsWithin_le_nhds
  have horder := hut.eventually_lt hvt hrs
  have hwin := hvt.eventually_lt (hut.add tendsto_const_nhds) hwidth
  have hvalue := ((hX s).tendsto.comp hv).sub ((hX r).tendsto.comp hu)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hvalue.norm
  apply le_of_tendsto hlim
  filter_upwards [horder, hwin] with n hn hw
  exact ofReal_norm_sub_le_denseWindowOscillation_grid hn.le hw ω

theorem ofReal_norm_sub_le_denseWindowOscillation_double_width
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {T δ r s : ℝ≥0} (hδ : 0 < δ) (hrs : r ≤ s) (hsT : s ≤ T)
    (hwidth : s ≤ r + δ) :
    ENNReal.ofReal ‖X s ω - X r ω‖ ≤ denseWindowOscillation X T (2 * δ) ω := by
  apply ofReal_norm_sub_le_denseWindowOscillation_of_rightContinuous hX hrs hsT
  have hd : δ < 2 * δ := by
    rw [two_mul]
    exact lt_add_of_pos_right δ hδ
  have hsum : r + δ < r + 2 * δ := by gcongr
  exact hwidth.trans_lt hsum

theorem norm_sub_le_toReal_denseWindowOscillation_double_width
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    {T δ r s : ℝ≥0} (hδ : 0 < δ) (hrs : r ≤ s) (hsT : s ≤ T)
    (hwidth : s ≤ r + δ) :
    ‖X s ω - X r ω‖ ≤ (denseWindowOscillation X T (2 * δ) ω).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (denseWindowOscillation_ne_top_of_cadlag hX T _)).mp
    (ofReal_norm_sub_le_denseWindowOscillation_double_width hX.1 hδ hrs hsT hwidth)

theorem IsCadlagPath.eventually_denseWindowOscillation_le_of_jumpProcess_bound
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b)
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ≥0} (hδ : Tendsto δ l (𝓝 0)) :
    ∀ᶠ i in l, denseWindowOscillation X T (δ i) ω ≤ ENNReal.ofReal (b + ε) := by
  obtain ⟨d, hd, hmod⟩ := hX.exists_short_window_norm_le_of_jumpProcess_bound T hb hε hj
  filter_upwards [hδ.eventually_le_const hd] with i hi
  apply denseWindowOscillation_le_of_bound
  intro r s hrs hsT hwin
  apply hmod r s hrs hsT
  have hsum : r + δ i ≤ r + d := by gcongr
  exact hwin.le.trans hsum

theorem IsCadlagPath.eventually_toReal_denseWindowOscillation_le_of_jumpProcess_bound
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hj : ∀ t, 0 < t → t ≤ T → ‖jumpProcess X t ω‖ ≤ b)
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ≥0} (hδ : Tendsto δ l (𝓝 0)) :
    ∀ᶠ i in l, (denseWindowOscillation X T (δ i) ω).toReal ≤ b + ε := by
  filter_upwards [hX.eventually_denseWindowOscillation_le_of_jumpProcess_bound T hb hε hj hδ]
    with i hi
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  simpa only [ENNReal.toReal_ofReal (add_nonneg hb hε.le)] using hle

end ProbabilityTheory
