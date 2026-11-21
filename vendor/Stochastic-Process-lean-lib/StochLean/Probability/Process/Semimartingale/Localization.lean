/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Stopping.LocalizingTail
public import StochLean.Probability.Process.Stopping.Finite
public import StochLean.Probability.Process.Path.Stopping

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.integral_congr_integrator_path (H : SimplePredictableRep F)
    {ω : Ω} (hXY : ∀ t, X t ω = Y t ω) : H.integral X ω = H.integral Y ω := by
  simp only [SimplePredictableRep.integral, hXY]

theorem IsSimplePredictable.elementaryIntegral_congr_integrator_path
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) {ω : Ω}
    (hXY : ∀ t, X t ω = Y t ω) : hH.elementaryIntegral X ω = hH.elementaryIntegral Y ω :=
  hH.choose.integral_congr_integrator_path hXY

theorem IsSimplePredictable.elementaryIntegral_congr_indistinguishable
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hXY : Indistinguishable X Y P) :
    hH.elementaryIntegral X =ᵐ[P] hH.elementaryIntegral Y :=
  hXY.mono fun _ hω ↦ hH.elementaryIntegral_congr_integrator_path hω

theorem IsGoodIntegrator.congr (hX : IsGoodIntegrator X F P) (hXY : Indistinguishable X Y P) :
    IsGoodIntegrator Y F P := by
  intro H hH hu
  exact TendstoInMeasure.congr_left
    (fun n ↦ (hH n).elementaryIntegral_congr_indistinguishable hXY) (hX H hH hu)

theorem IsTotalSemimartingale.congr_of_adapted (hX : IsTotalSemimartingale X F P)
    (hXY : Indistinguishable X Y P) (ha : Adapted F Y) : IsTotalSemimartingale Y F P :=
  ⟨ha, HasCadlagPaths.congr hXY hX.2.1, hX.2.2.congr hXY⟩

theorem IsSemimartingale.congr_of_adapted (hX : IsSemimartingale X F P)
    (hXY : Indistinguishable X Y P) (ha : Adapted F Y) : IsSemimartingale Y F P := by
  intro T
  apply (hX T).congr_of_adapted (hXY.stoppedProcess _) ?_
  intro t
  change Measurable[F t] (fun ω ↦ Y (min t T) ω)
  exact (ha _).mono (F.mono (min_le_left t T)) le_rfl

/-- The exceptional sets need not be measurable: the proof uses outer-measure bounds only. -/
theorem isGoodIntegrator_of_eq_off_small_sets (Y : ℕ → ℝ≥0 → Ω → ℝ) (E : ℕ → Set Ω)
    (hY : ∀ n, IsGoodIntegrator (Y n) F P)
    (heq : ∀ n ω, ω ∉ E n → ∀ t, X t ω = Y n t ω)
    (hsmall : Tendsto (fun n ↦ P (E n)) atTop (𝓝 0)) : IsGoodIntegrator X F P := by
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  obtain ⟨n, hn⟩ := (hsmall.eventually_lt_const (ENNReal.half_pos hη.ne')).exists
  obtain ⟨δ, hδ, hb⟩ := (isGoodIntegrator_iff_continuousAtZero.mp (hY n))
    ε hε (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  have hs : {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} ⊆
      E n ∪ {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖} := by
    intro ω hω
    by_cases hE : ω ∈ E n
    · exact Or.inl hE
    · exact Or.inr (by
        change ε ≤ ‖hH.elementaryIntegral (Y n) ω‖
        rw [← hH.elementaryIntegral_congr_integrator_path (heq n ω hE)]
        exact hω)
  calc
    _ ≤ P (E n ∪ {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖}) := measure_mono hs
    _ ≤ P (E n) + P {ω | ε ≤ ‖hH.elementaryIntegral (Y n) ω‖} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hn.le (hb H hH hbound)
    _ = η := ENNReal.add_halves η

/-- Common-event AE agreement suffices; its null exception is added to each small set. -/
theorem isGoodIntegrator_of_ae_eq_off_small_sets (Y : ℕ → ℝ≥0 → Ω → ℝ) (E : ℕ → Set Ω)
    (hY : ∀ n, IsGoodIntegrator (Y n) F P)
    (heq : ∀ n, ∀ᵐ ω ∂P, ω ∉ E n → ∀ t, X t ω = Y n t ω)
    (hsmall : Tendsto (fun n ↦ P (E n)) atTop (𝓝 0)) : IsGoodIntegrator X F P := by
  let bad := fun n ↦ {ω | ¬ (ω ∉ E n → ∀ t, X t ω = Y n t ω)}
  have hbad : ∀ n, P (bad n) = 0 := fun n ↦ ae_iff.mp (heq n)
  have hmass : ∀ n, P (E n ∪ bad n) = P (E n) := by
    intro n
    apply le_antisymm _ (measure_mono subset_union_left)
    calc
      _ ≤ P (E n) + P (bad n) := measure_union_le _ _
      _ = P (E n) := by rw [hbad, add_zero]
  apply isGoodIntegrator_of_eq_off_small_sets Y (fun n ↦ E n ∪ bad n) hY
  · intro n ω hω
    have hn : ω ∉ E n := fun h ↦ hω (Or.inl h)
    have hb : ω ∉ bad n := fun h ↦ hω (Or.inr h)
    exact (not_not.mp hb) hn
  · simpa only [hmass] using hsmall

variable [IsFiniteMeasure P]

/-- Protter II.6's patching argument only needs agreement strictly before the lifetimes.
These are measurable random variables, not necessarily stopping times; neither positivity
nor monotonicity is needed beyond their AE divergence to infinity. -/
theorem isSemimartingale_of_ae_agree_before_lifetimes (ha : Adapted F X)
    (hc : HasCadlagPaths X P)
    (Y : ℕ → ℝ≥0 → Ω → ℝ) (hY : ∀ n, IsSemimartingale (Y n) F P)
    (τ : ℕ → Ω → WithTop ℝ≥0) (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (heq : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < τ n ω → X t ω = Y n t ω) :
    IsSemimartingale X F P := by
  intro T
  change IsTotalSemimartingale (stoppedProcess X (FiniteStoppingTime.const F T).withTop) F P
  rw [FiniteStoppingTime.stoppedProcess_eq]
  refine ⟨fun t ↦ (ha _).mono (F.mono (min_le_left t T)) le_rfl,
    hc.mono (fun _ h ↦ h.min_const T), ?_⟩
  apply isGoodIntegrator_of_ae_eq_off_small_sets (fun n t ↦ Y n (min t T))
    (fun n ↦ {ω | τ n ω ≤ T}) ?_ ?_ (tendsto_measure_le_of_ae_tendsto_top hm hlim T)
  · intro n
    have h := (hY n T).2.2
    change IsGoodIntegrator (stoppedProcess (Y n) (FiniteStoppingTime.const F T).withTop) F P at h
    rwa [FiniteStoppingTime.stoppedProcess_eq] at h
  · intro n
    filter_upwards [heq n] with ω hω hn t
    exact hω (min t T)
      ((WithTop.coe_le_coe.mpr (min_le_right t T)).trans_lt (lt_of_not_ge hn))

theorem isSemimartingale_of_agree_before_lifetimes (ha : Adapted F X) (hc : HasCadlagPaths X P)
    (Y : ℕ → ℝ≥0 → Ω → ℝ) (hY : ∀ n, IsSemimartingale (Y n) F P)
    (τ : ℕ → Ω → WithTop ℝ≥0) (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (heq : ∀ n ω (t : ℝ≥0), (t : WithTop ℝ≥0) < τ n ω → X t ω = Y n t ω) :
    IsSemimartingale X F P :=
  isSemimartingale_of_ae_agree_before_lifetimes ha hc Y hY τ hm hlim
    (fun n ↦ ae_of_all _ (heq n))

/-- Ordinary semimartingales can be patched from their masked localizations. Neither
monotonicity of the pre-localizing sequence nor a decomposition is used here. -/
theorem isSemimartingale_of_preLocalizingSequence (ha : Adapted F X) (hc : HasCadlagPaths X P)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsPreLocalizingSequence F τ P)
    (hY : ∀ n, IsSemimartingale
      (stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n)) F P) :
    IsSemimartingale X F P := by
  intro T
  change IsTotalSemimartingale (stoppedProcess X (FiniteStoppingTime.const F T).withTop) F P
  rw [FiniteStoppingTime.stoppedProcess_eq]
  refine ⟨fun t ↦ (ha _).mono (F.mono (min_le_left t T)) le_rfl,
    hc.mono (fun _ h ↦ h.min_const T), ?_⟩
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n)
  apply isGoodIntegrator_of_eq_off_small_sets (fun n t ↦ Y n (min t T))
    (fun n ↦ {ω | τ n ω ≤ T}) ?_ ?_ (hτ.tendsto_measure_le T)
  · intro n
    have h := (hY n T).2.2
    change IsGoodIntegrator (stoppedProcess (Y n) (FiniteStoppingTime.const F T).withTop) F P at h
    rwa [FiniteStoppingTime.stoppedProcess_eq] at h
  · intro n ω hn t
    have hT : (T : WithTop ℝ≥0) < τ n ω := lt_of_not_ge hn
    have hp : 0 < τ n ω := lt_of_le_of_lt bot_le hT
    have ht : (min t T : WithTop ℝ≥0) ≤ τ n ω :=
      (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans hT.le
    dsimp only [Y]
    rw [stoppedProcess_eq_of_le ht, indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hp)]
    rfl

theorem isSemimartingale_of_locally_semimartingale (ha : Adapted F X) (hc : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsSemimartingale Y F P) F X P) : IsSemimartingale X F P := by
  obtain ⟨τ, hτ, hY⟩ := hL
  exact isSemimartingale_of_preLocalizingSequence ha hc hτ.toIsPreLocalizingSequence hY

end ProbabilityTheory
