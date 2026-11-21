/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularConditionalModulusOrdered
public import StochLean.Probability.Martingale.Doob.ShiftedConditionalSequence
public import StochLean.Probability.Process.ClassD.Bounded
public import StochLean.ForMathlib.MeasureTheory.Function.FiniteTailBounds

/-! # Compact conditional moduli for regular bounded supermartingales

Zero means of actual positive predictable jumps give vanishing compact signed
conditional moduli. The coherent projection residuals and their valid stopping
identities are constructed from the original source process. There is no TI,
candidate compensator, candidate residual or assumed convergence premise.
An antitone positive cofinal width sequence gives the full zero-width filter
limit. Real conversion is used only after the actual modulus is proved finite.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ} {T : ℝ≥0}

/-- Along decreasing widths, the source compact conditional modulus tends to
zero using the actual coherent signed residual and its first-threshold bound. -/
theorem Supermartingale.tendsto_measureReal_conditionalModulus_of_predictable_jump_mean_zero_seq
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {δ : ℕ → ℝ≥0} (hδmono : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0))
    {W : ℕ → Ω → ℝ≥0∞} (hW : ∀ n, IsConditionalIncrementModulus F P X T (δ n) (W n))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | ENNReal.ofReal a < W n ω}) atTop (𝓝 0) := by
  obtain ⟨R, haR, hcR, hbR, hmR, heR, hsR⟩ :=
    hX.exists_coherent_conditional_residuals_of_bound hF hc hN hb δ hδmono
  have hD := hX.isClassD_of_bound hc.hasRightContinuousPaths hb
  have hlim := hX.tendsto_measureReal_denseRunningSupremum_of_ordered_conditional_increments
    hD hc hF hreg hδ haR (fun n ω ↦ (hcR n ω).1)
    (fun n ↦ Eventually.of_forall fun ω t ↦ (hbR n ω t).1) hmR hsR T ha
  have hbound (n : ℕ) : W n ≤ᵐ[P] denseRunningSupremum (R n) T := by
    let Q := X - R n
    have hrQ : HasRightContinuousPaths Q P := by
      filter_upwards [hc] with ω hω t
      exact (hω.1 t).sub ((hcR n ω).1 t)
    have heQ (t : ℝ≥0) : Q t =ᵐ[P] P[X (t + δ n) | F t] := by
      filter_upwards [heR n t] with ω hω
      change X t ω - R n t ω = _
      simp only [Pi.sub_apply] at hω
      linarith only [hω]
    have hd := hX.ae_conditionalIncrementModulus_le_denseRunningSupremum
      hc.hasRightContinuousPaths hrQ heQ (hW n)
    have he : X - Q = R n := by
      funext t ω
      change X t ω - (X t ω - R n t ω) = R n t ω
      ring
    rwa [he] at hd
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hlim
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbound n] with ω hω hmem
  exact hmem.trans_le hω

/-- The full width-to-zero limit, not only convergence along one selected grid. -/
theorem Supermartingale.tendsto_measureReal_conditionalModulus_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < W δ ω}) (𝓝 0) (𝓝 0) := by
  let d : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdmono : Antitone d := by
    intro n m hnm
    dsimp [d]
    gcongr
  have hseq := hX.tendsto_measureReal_conditionalModulus_of_predictable_jump_mean_zero_seq
    hF hc hN hb hreg hdmono hd (fun n ↦ hW (d n)) ha
  have hmono : Monotone (fun δ ↦ P.real {ω | ENNReal.ofReal a < W δ ω}) := by
    intro δ η hδη
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [(hW δ).mono_width (hW η) hδη] with ω hω hmem
    exact hmem.trans_le hω
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    obtain ⟨n, hn⟩ := (hseq.eventually_lt_const hz).exists
    filter_upwards [Iio_mem_nhds (hdpos n)] with δ hδ
    exact (hmono hδ.le).trans_lt hn

/-- Native convergence in probability of every version of the actual compact
modulus, with its extended value proved finite before real conversion. -/
theorem Supermartingale.tendstoInMeasure_conditionalModulus_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ)) :
    TendstoInMeasure P (fun δ ω ↦ (W δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_zero_of_nonneg_of_measureReal_gt
    (fun _ ↦ Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  intro a ha
  have hfin (δ : ℝ≥0) : ∀ᵐ ω ∂P, W δ ω ≠ ∞ :=
    (hW δ).ae_ne_top_of_norm_bound (fun t _ ↦ hX.integrable t)
      (fun t _ ↦ hb.mono fun _ hω ↦ hω t)
  have he (δ : ℝ≥0) : P.real {ω | ENNReal.ofReal a < W δ ω} =
      P.real {ω | a < (W δ ω).toReal} := by
    apply measureReal_congr
    filter_upwards [hfin δ] with ω hω
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal ha.le hω)
  exact (hX.tendsto_measureReal_conditionalModulus_of_predictable_jump_mean_zero
    hF hc hN hb hreg hW ha).congr' (Eventually.of_forall he)

end MeasureTheory
