/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.KlenkeBridge
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartStopping
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUnbounded
public import StochLean.Probability.Martingale.Convergence.InMeasure
public import StochLean.Probability.Process.LocalMartingale.LocalizationUpTo
public import StochLean.Probability.Process.Stopping.FiniteSampleMeasurability
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableL2

/-! # Klenke 21.75--21.76: stopping and bracket moments

The local-martingale predicate in this library deliberately permits a nonintegrable
time-zero value.  Accordingly, the two conclusions of Klenke 21.75 are kept separate:
integrability of `M 0` is enough for the stopped expectation identity, whereas an
`L²` assumption on `M 0` is needed for the stopped process itself to be an
`L²`-bounded martingale.

The bracket in this file is Klenke's normalized, zero-initial continuous bracket.
No second quadratic-variation owner is introduced.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
  {M : ℝ≥0 → Ω → ℝ}

/-- One-use witness that `M` is a continuous local martingale up to the random
lifetime `κ`, with normalized bracket `Q`.  This is deliberately not a second
local-martingale hierarchy.  Its localizers act on the centered process, so an
unbounded `M 0` is never claimed to become bounded merely by stopping.

The last field is the stopped bracket moment identity on each genuine `L²`
localization.  It is the source-facing content of the notation `⟨M⟩` before
`κ`, expressed without constructing another permanent quadratic-variation
owner. -/
structure KlenkeContinuousLocalMartingaleUpToWitness
    (M : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (κ : Ω → WithTop ℝ≥0) (Q : ℝ≥0 → Ω → ℝ) where
  adapted : Adapted F M
  continuous : HasContinuousPaths M P
  bracket_adapted : Adapted F Q
  bracket_continuous : HasContinuousPaths Q P
  bracket_zero : Q 0 = 0
  bracket_monotone : ∀ ω, Monotone (fun t ↦ Q t ω)
  localizer : ℕ → Ω → WithTop ℝ≥0
  localizer_isStoppingTime : ∀ n, IsStoppingTime F (localizer n)
  localizer_monotone : Monotone localizer
  localizer_tendsto_lifetime : ∀ᵐ ω ∂P, Tendsto (localizer · ω) atTop (𝓝 (κ ω))
  centered_localizer_bounded : ∀ n, ∃ C : ℝ≥0, ∀ᵐ ω ∂P, ∀ t,
    ‖MeasureTheory.stoppedProcess (fun s ω ↦ M s ω - M 0 ω) (localizer n) t ω‖ ≤ C
  centered_localizer_squareIntegrable : ∀ n,
    IsSquareIntegrableMartingale
      (MeasureTheory.stoppedProcess (fun s ω ↦ M s ω - M 0 ω) (localizer n)) F P
  centered_stopped_bracket_moment : ∀ n (ρ : FiniteStoppingTime F),
    (∫ ω, MeasureTheory.stoppedProcess (fun s ω ↦ M s ω - M 0 ω)
        (localizer n) (ρ ω) ω ^ 2 ∂P) =
      ∫ ω, MeasureTheory.stoppedProcess Q (localizer n) (ρ ω) ω ∂P

omit [IsProbabilityMeasure P] in
private theorem memLp_two_and_integral_sq_le_of_ae_tendsto
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, MemLp (f n) 2 P) (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (hC : 0 ≤ C) (hb : ∀ n, (∫ ω, f n ω ^ 2 ∂P) ≤ C) :
    MemLp g 2 P ∧ (∫ ω, g ω ^ 2 ∂P) ≤ C := by
  have hlimsq : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω ^ 2) atTop (𝓝 (g ω ^ 2)) :=
    hlim.mono fun _ hω ↦ hω.pow 2
  have hFatou : (∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (f n ω ^ 2)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hlimsq] with ω hω
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P) atTop :=
        lintegral_liminf_le' fun n ↦
          (hf n).integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le
        (Eventually.of_forall (fun n ↦ by
          rw [← ofReal_integral_eq_lintegral_ofReal (hf n).integrable_sq
            (ae_of_all P fun ω ↦ sq_nonneg (f n ω))]
          exact ENNReal.ofReal_le_ofReal (hb n))).frequently
  have hgi : Integrable (fun ω ↦ g ω ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable (hg.pow 2)
      (ae_of_all P fun ω ↦ sq_nonneg (g ω))).mp
        (hFatou.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨(memLp_two_iff_integrable_sq hg).2 hgi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all P fun ω ↦ sq_nonneg (g ω))]
  exact hFatou

/-- Random-lifetime core of Klenke 21.75.  A sequence of centered bounded `L²`
localizations tending to `κ` is enough to make the process stopped at every
everywhere-finite `τ₀ < κ` an `L²`-bounded martingale. -/
theorem KlenkeContinuousLocalMartingaleUpToWitness.centered_stoppedProcess_l2_bounded
    {κ : Ω → WithTop ℝ≥0} {Q : ℝ≥0 → Ω → ℝ}
    (hM : KlenkeContinuousLocalMartingaleUpToWitness M F P κ Q)
    (hF : F.IsUsual P) (τ₀ : FiniteStoppingTime F)
    (hlt : ∀ᵐ ω ∂P, τ₀.withTop ω < κ ω)
    (hQ : Integrable (fun ω ↦ Q (τ₀ ω) ω) P) :
    IsSquareIntegrableMartingale
        (MeasureTheory.stoppedProcess (fun t ω ↦ M t ω - M 0 ω) τ₀.withTop) F P ∧
      ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess
          (fun s ω ↦ M s ω - M 0 ω) τ₀.withTop t ω ^ 2 ∂P) ≤
            ∫ ω, Q (τ₀ ω) ω ∂P := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ M t ω - M 0 ω
  let L : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    MeasureTheory.stoppedProcess N (hM.localizer n)
  let X : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    MeasureTheory.stoppedProcess (L n) τ₀.withTop
  let Y : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess N τ₀.withTop
  have hNc : HasContinuousPaths N P := by
    filter_upwards [hM.continuous] with ω hω
    exact hω.sub continuous_const
  have hNa : Adapted F N := fun t ↦
    (hM.adapted t).sub ((hM.adapted 0).mono (F.mono bot_le) le_rfl)
  have hXL2 (n : ℕ) : IsSquareIntegrableMartingale (X n) F P := by
    apply (hM.centered_localizer_squareIntegrable n).stoppedProcess_of_usual hF
      (hNc.stoppedProcess (hM.localizer n)).hasRightContinuousPaths τ₀.isStoppingTime
  have hC : 0 ≤ ∫ ω, Q (τ₀ ω) ω ∂P := integral_nonneg fun ω ↦ by
    calc
      (0 : ℝ) = Q 0 ω := (congrFun hM.bracket_zero ω).symm
      _ ≤ Q (τ₀ ω) ω := hM.bracket_monotone ω bot_le
  have hXbound (n : ℕ) (t : ℝ≥0) :
      (∫ ω, X n t ω ^ 2 ∂P) ≤ ∫ ω, Q (τ₀ ω) ω ∂P := by
    let ρ := FiniteStoppingTime.truncate τ₀.isStoppingTime t
    have henergy := hM.centered_stopped_bracket_moment n ρ
    have heX :
        (fun ω ↦ MeasureTheory.stoppedProcess N (hM.localizer n) (ρ ω) ω) =
          X n t := by
      change (fun ω ↦ MeasureTheory.stoppedProcess N (hM.localizer n) (ρ ω) ω) =
        MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess N (hM.localizer n)) τ₀.withTop t
      rw [show τ₀.withTop = (fun ω ↦ (τ₀ ω : WithTop ℝ≥0)) by rfl]
      simpa only [ρ] using
        (FiniteStoppingTime.stoppedValue_truncate
          (MeasureTheory.stoppedProcess N (hM.localizer n)) τ₀.isStoppingTime t)
    have heQ :
        (fun ω ↦ MeasureTheory.stoppedProcess Q (hM.localizer n) (ρ ω) ω) =
          fun ω ↦ MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess Q (hM.localizer n)) τ₀.withTop t ω := by
      rw [show τ₀.withTop = (fun ω ↦ (τ₀ ω : WithTop ℝ≥0)) by rfl]
      simpa only [ρ] using
        (FiniteStoppingTime.stoppedValue_truncate
          (MeasureTheory.stoppedProcess Q (hM.localizer n)) τ₀.isStoppingTime t)
    have henergy' : (∫ ω, X n t ω ^ 2 ∂P) =
        ∫ ω, MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess Q (hM.localizer n)) τ₀.withTop t ω ∂P := by
      calc
        _ = ∫ ω, MeasureTheory.stoppedProcess N
              (hM.localizer n) (ρ ω) ω ^ 2 ∂P := by
          apply integral_congr_ae
          exact ae_of_all P fun ω ↦ congrArg (fun x : ℝ ↦ x ^ 2) (congrFun heX ω).symm
        _ = ∫ ω, MeasureTheory.stoppedProcess Q
              (hM.localizer n) (ρ ω) ω ∂P := henergy
        _ = _ := integral_congr_ae (ae_of_all P fun ω ↦ congrFun heQ ω)
    have hQnSA := hM.bracket_adapted.stronglyAdapted.stoppedProcess_of_usual hF
      hM.bracket_continuous.hasRightContinuousPaths (hM.localizer_isStoppingTime n)
    have hQnC := hM.bracket_continuous.stoppedProcess (hM.localizer n)
    have hQntSA := hQnSA.stoppedProcess_of_usual hF hQnC.hasRightContinuousPaths
      τ₀.isStoppingTime
    have hsample : Integrable (fun ω ↦ MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess Q (hM.localizer n)) τ₀.withTop t ω) P := by
      apply hQ.mono' (((hQntSA t).mono (F.le t)).aestronglyMeasurable)
      filter_upwards with ω
      let u := WithTop.untopA (min (t : WithTop ℝ≥0) (τ₀.withTop ω))
      let v := WithTop.untopA (min (u : WithTop ℝ≥0) (hM.localizer n ω))
      have hu : u ≤ τ₀ ω := WithTop.untopA_le (min_le_right _ _)
      have hv : v ≤ u := WithTop.untopA_le (min_le_left _ _)
      have hqv : 0 ≤ Q v ω := by
        calc
          (0 : ℝ) = Q 0 ω := (congrFun hM.bracket_zero ω).symm
          _ ≤ Q v ω := hM.bracket_monotone ω bot_le
      change ‖Q v ω‖ ≤ Q (τ₀ ω) ω
      rw [Real.norm_eq_abs, abs_of_nonneg hqv]
      exact hM.bracket_monotone ω (hv.trans hu)
    rw [henergy']
    apply integral_mono_ae hsample hQ
    filter_upwards with ω
    let u := WithTop.untopA (min (t : WithTop ℝ≥0) (τ₀.withTop ω))
    let v := WithTop.untopA (min (u : WithTop ℝ≥0) (hM.localizer n ω))
    have hu : u ≤ τ₀ ω := WithTop.untopA_le (min_le_right _ _)
    have hv : v ≤ u := WithTop.untopA_le (min_le_left _ _)
    change Q v ω ≤ Q (τ₀ ω) ω
    exact hM.bracket_monotone ω (hv.trans hu)
  have hXlim (t : ℝ≥0) : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ X n t ω) atTop (𝓝 (Y t ω)) := by
    filter_upwards [hM.localizer_tendsto_lifetime, hlt] with ω hσω hτω
    let u := min t (τ₀ ω)
    have huκ : (u : WithTop ℝ≥0) < κ ω :=
      (WithTop.coe_le_coe.mpr (min_le_right _ _)).trans_lt hτω
    apply tendsto_const_nhds.congr'
    filter_upwards [hσω.eventually (Ioi_mem_nhds huκ)] with n hn
    simp only [X, Y, FiniteStoppingTime.stoppedProcess_eq]
    change N u ω = MeasureTheory.stoppedProcess N (hM.localizer n) u ω
    exact (stoppedProcess_eq_of_le hn.le).symm
  have hYSA : StronglyAdapted F Y :=
    hNa.stronglyAdapted.stoppedProcess_of_usual hF hNc.hasRightContinuousPaths
      τ₀.isStoppingTime
  let C : ℝ≥0 := ⟨∫ ω, Q (τ₀ ω) ω ∂P, hC⟩
  have hXUI (t : ℝ≥0) : UniformIntegrable (fun n ↦ X n t) 1 P :=
    uniformIntegrable_of_bounded_integral_sq (fun n ↦ (hXL2 n).2 t) C
      (fun n ↦ hXbound n t)
  have hYm : Martingale Y F P :=
    martingale_of_tendstoInMeasure_uniformIntegrable (fun n ↦ (hXL2 n).1) hYSA hXUI
      (fun t ↦ tendstoInMeasure_of_tendsto_ae
        (fun n ↦ ((hXL2 n).1.integrable t).aestronglyMeasurable) (hXlim t))
  have hYL (t : ℝ≥0) : MemLp (Y t) 2 P ∧
      (∫ ω, Y t ω ^ 2 ∂P) ≤ ∫ ω, Q (τ₀ ω) ω ∂P :=
    memLp_two_and_integral_sq_le_of_ae_tendsto (fun n ↦ (hXL2 n).2 t)
      (((hYSA t).mono (F.le t)).aestronglyMeasurable) (hXlim t) hC
      (fun n ↦ hXbound n t)
  exact ⟨⟨hYm, fun t ↦ (hYL t).1⟩, fun t ↦ (hYL t).2⟩

/-- Random-lifetime expectation clause of Klenke 21.75.  In the native
masked-local-martingale semantics the source's implicit initial integrability
is stated explicitly. -/
theorem KlenkeContinuousLocalMartingaleUpToWitness.integrable_stoppedValue_and_integral_eq_initial
    {κ : Ω → WithTop ℝ≥0} {Q : ℝ≥0 → Ω → ℝ}
    (hM : KlenkeContinuousLocalMartingaleUpToWitness M F P κ Q)
    (hF : F.IsUsual P) (h0 : Integrable (M 0) P)
    (τ₀ : FiniteStoppingTime F) (hlt : ∀ᵐ ω ∂P, τ₀.withTop ω < κ ω)
    (hQ : Integrable (fun ω ↦ Q (τ₀ ω) ω) P) :
    Integrable (fun ω ↦ M (τ₀ ω) ω) P ∧
      (∫ ω, M (τ₀ ω) ω ∂P) = ∫ ω, M 0 ω ∂P := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ M t ω - M 0 ω
  let Y : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess N τ₀.withTop
  have hNc : HasContinuousPaths N P := by
    filter_upwards [hM.continuous] with ω hω
    exact hω.sub continuous_const
  have hcenter := hM.centered_stoppedProcess_l2_bounded hF τ₀ hlt hQ
  have hC : 0 ≤ ∫ ω, Q (τ₀ ω) ω ∂P := integral_nonneg fun ω ↦ by
    calc
      (0 : ℝ) = Q 0 ω := (congrFun hM.bracket_zero ω).symm
      _ ≤ Q (τ₀ ω) ω := hM.bracket_monotone ω bot_le
  let C : ℝ≥0 := ⟨∫ ω, Q (τ₀ ω) ω ∂P, hC⟩
  have hUI : UniformIntegrable Y 1 P :=
    uniformIntegrable_of_bounded_integral_sq hcenter.1.2 C hcenter.2
  have hfinite : ∀ᵐ ω ∂P, τ₀.withTop ω ≠ ⊤ := ae_of_all P τ₀.withTop_ne_top
  have hterminalUI : UniformIntegrable
      (fun _ : Unit ↦ stoppedValue Y τ₀.withTop) 1 P :=
    hcenter.1.1.uniformIntegrable_stoppedValue_of_ae_finite_usual hUI hF
      (hNc.stoppedProcess τ₀.withTop).hasRightContinuousPaths
      (fun _ ↦ τ₀.isStoppingTime) (fun _ ↦ hfinite)
  have hterminal : stoppedValue Y τ₀.withTop = fun ω ↦ M (τ₀ ω) ω - M 0 ω := by
    simp only [Y, FiniteStoppingTime.stoppedValue_eq,
      FiniteStoppingTime.stoppedProcess_eq, min_self, N]
  have hdiff : Integrable (fun ω ↦ M (τ₀ ω) ω - M 0 ω) P :=
    memLp_one_iff_integrable.mp ((hterminalUI.memLp ()).ae_eq
      (ae_of_all P fun ω ↦ congrFun hterminal ω))
  have hτint : Integrable (fun ω ↦ M (τ₀ ω) ω) P := by
    apply (hdiff.add h0).congr
    filter_upwards with ω
    simp only [Pi.add_apply]
    ring
  refine ⟨hτint, ?_⟩
  let ρ := FiniteStoppingTime.const F 0
  have hsample := hcenter.1.1.stoppedValue_ae_eq_condExp_of_ae_finite_usual hUI hF
    (hNc.stoppedProcess τ₀.withTop).hasRightContinuousPaths
      ρ.isStoppingTime τ₀.isStoppingTime (ae_of_all P fun _ ↦ bot_le) hfinite
  have hmean :
      (∫ ω, stoppedValue Y ρ.withTop ω ∂P) =
        ∫ ω, stoppedValue Y τ₀.withTop ω ∂P := by
    calc
      _ = ∫ ω, P[stoppedValue Y τ₀.withTop | ρ.measurableSpace] ω ∂P :=
        integral_congr_ae hsample
      _ = _ := integral_condExp ρ.measurableSpace_le
  have hinitial : stoppedValue Y ρ.withTop = fun _ ↦ 0 := by
    funext ω
    simp [ρ, Y, N, FiniteStoppingTime.stoppedValue_eq,
      FiniteStoppingTime.stoppedProcess_eq]
  have hcenterMean : (∫ ω, M (τ₀ ω) ω - M 0 ω ∂P) = 0 := by
    calc
      _ = ∫ ω, stoppedValue Y τ₀.withTop ω ∂P := by rw [hterminal]
      _ = ∫ ω, stoppedValue Y ρ.withTop ω ∂P := hmean.symm
      _ = 0 := by rw [hinitial, integral_zero]
  have hsub := integral_sub hτint h0
  calc
    (∫ ω, M (τ₀ ω) ω ∂P) =
        ((∫ ω, M (τ₀ ω) ω ∂P) - ∫ ω, M 0 ω ∂P) + ∫ ω, M 0 ω ∂P := by ring
    _ = (∫ ω, M (τ₀ ω) ω - M 0 ω ∂P) + ∫ ω, M 0 ω ∂P := by rw [hsub]
    _ = ∫ ω, M 0 ω ∂P := by rw [hcenterMean, zero_add]

/-- Random-lifetime `L²` clause of Klenke 21.75.  The returned real bound is
uniform over deterministic time; the factor-two estimate avoids imposing any
extra orthogonality API on the lightweight up-to-lifetime witness. -/
theorem KlenkeContinuousLocalMartingaleUpToWitness.squareIntegrable_stoppedProcess_l2_bounded
    {κ : Ω → WithTop ℝ≥0} {Q : ℝ≥0 → Ω → ℝ}
    (hM : KlenkeContinuousLocalMartingaleUpToWitness M F P κ Q)
    (hF : F.IsUsual P) (h0 : MemLp (M 0) 2 P)
    (τ₀ : FiniteStoppingTime F) (hlt : ∀ᵐ ω ∂P, τ₀.withTop ω < κ ω)
    (hQ : Integrable (fun ω ↦ Q (τ₀ ω) ω) P) :
    IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess M τ₀.withTop) F P ∧
      ∃ C : ℝ, ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess M τ₀.withTop t ω ^ 2 ∂P) ≤ C := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ M t ω - M 0 ω
  let Y : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess N τ₀.withTop
  let Z : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess M τ₀.withTop
  have hcenter := hM.centered_stoppedProcess_l2_bounded hF τ₀ hlt hQ
  have hZSA : StronglyAdapted F Z :=
    hM.adapted.stronglyAdapted.stoppedProcess_of_usual hF
      hM.continuous.hasRightContinuousPaths τ₀.isStoppingTime
  have hconst : Martingale (fun _ : ℝ≥0 ↦ M 0) F P :=
    martingale_const_fun F P (hM.adapted 0).stronglyMeasurable
      (h0.integrable one_le_two)
  have hdecomp (t : ℝ≥0) (ω : Ω) : Z t ω = Y t ω + M 0 ω := by
    simp only [Z, Y, N, MeasureTheory.stoppedProcess]
    ring
  have hZm : Martingale Z F P := by
    apply (hcenter.1.1.add hconst).congr hZSA
    intro t
    filter_upwards with ω
    exact (hdecomp t ω).symm
  have hZL (t : ℝ≥0) : MemLp (Z t) 2 P := by
    have hsumLp : MemLp (Y t + fun ω ↦ M 0 ω) 2 P :=
      (hcenter.1.2 t).add h0
    exact MemLp.ae_eq (ae_of_all P fun ω ↦ (hdecomp t ω).symm) hsumLp
  refine ⟨⟨hZm, hZL⟩,
    2 * (∫ ω, Q (τ₀ ω) ω ∂P) + 2 * (∫ ω, M 0 ω ^ 2 ∂P), fun t ↦ ?_⟩
  have hiY := (hcenter.1.2 t).integrable_sq
  have hi0 := h0.integrable_sq
  have hiZ := (hZL t).integrable_sq
  have hpoint : (fun ω ↦ Z t ω ^ 2) ≤ᵐ[P]
      fun ω ↦ 2 * Y t ω ^ 2 + 2 * M 0 ω ^ 2 := by
    filter_upwards with ω
    rw [hdecomp]
    nlinarith only [sq_nonneg (Y t ω - M 0 ω)]
  calc
    (∫ ω, Z t ω ^ 2 ∂P) ≤ ∫ ω, 2 * Y t ω ^ 2 + 2 * M 0 ω ^ 2 ∂P :=
      integral_mono_ae hiZ ((hiY.const_mul 2).add (hi0.const_mul 2)) hpoint
    _ = 2 * (∫ ω, Y t ω ^ 2 ∂P) + 2 * (∫ ω, M 0 ω ^ 2 ∂P) := by
      rw [integral_add (hiY.const_mul 2) (hi0.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * (∫ ω, Q (τ₀ ω) ω ∂P) + 2 * (∫ ω, M 0 ω ^ 2 ∂P) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hcenter.2 t) (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl

/-- Full source-facing random-lifetime form of Klenke Theorem 21.75. -/
theorem KlenkeContinuousLocalMartingaleUpToWitness.klenke_21_75
    {κ : Ω → WithTop ℝ≥0} {Q : ℝ≥0 → Ω → ℝ}
    (hM : KlenkeContinuousLocalMartingaleUpToWitness M F P κ Q)
    (hF : F.IsUsual P) (h0 : MemLp (M 0) 2 P)
    (τ₀ : FiniteStoppingTime F) (hlt : ∀ᵐ ω ∂P, τ₀.withTop ω < κ ω)
    (hQ : Integrable (fun ω ↦ Q (τ₀ ω) ω) P) :
    Integrable (fun ω ↦ M (τ₀ ω) ω) P ∧
      (∫ ω, M (τ₀ ω) ω ∂P) = ∫ ω, M 0 ω ∂P ∧
      IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess M τ₀.withTop) F P ∧
      ∃ C : ℝ, ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess M τ₀.withTop t ω ^ 2 ∂P) ≤ C := by
  have hmean := hM.integrable_stoppedValue_and_integral_eq_initial
    hF (h0.integrable one_le_two) τ₀ hlt hQ
  have hL2 := hM.squareIntegrable_stoppedProcess_l2_bounded hF h0 τ₀ hlt hQ
  exact ⟨hmean.1, hmean.2, hL2.1, hL2.2⟩

private theorem IsContinuousLocalMartingale.klenkeSquareVariation_sub_initial
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P) :
    Indistinguishable
      ((hM.sub_initial hF).isSemimartingale hF |>.continuousQuadraticVariation hF)
      (hM.klenkeSquareVariation hF) P := by
  have hconst : HasFiniteVariationPaths (fun _ : ℝ≥0 ↦ M 0) P :=
    (show HasMonotonePaths (fun _ : ℝ≥0 ↦ M 0) P from
      ae_of_all P fun _ _ _ _ ↦ le_rfl).hasFiniteVariationPaths
  simpa only [Pi.sub_apply, IsContinuousLocalMartingale.klenkeSquareVariation] using
    (hM.isSemimartingale hF).continuousQuadraticVariation_sub_finiteVariation
      (isSemimartingale_const_initial (hM.1.1 0)) hF hconst

private theorem IsContinuousLocalMartingale.stopped_continuousQuadraticVariation_ae_le
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) (t : ℝ≥0) :
    ((hM.stoppedProcess hF τ.isStoppingTime).isSemimartingale hF
        |>.continuousQuadraticVariation hF t) ≤ᵐ[P]
      fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω := by
  have hstop := (hM.isSemimartingale hF).continuousQuadraticVariation_stoppedProcess
    hF τ.isStoppingTime
  filter_upwards [hstop.ae_eq t] with ω hω
  rw [hω]
  change hM.klenkeSquareVariation hF (min t (τ ω)) ω ≤
    hM.klenkeSquareVariation hF (τ ω) ω
  exact hM.monotone_klenkeSquareVariation hF ω (min_le_right _ _)

/-- Finite expected normalized bracket at `τ` makes every deterministic-time
bracket value of the stopped process integrable.  This is the bracket input
used in Klenke 21.75. -/
theorem IsContinuousLocalMartingale.integrable_stopped_continuousQuadraticVariation
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P)
    (t : ℝ≥0) :
    Integrable
      ((hM.stoppedProcess hF τ.isStoppingTime).isSemimartingale hF
        |>.continuousQuadraticVariation hF t) P := by
  let hS := hM.stoppedProcess hF τ.isStoppingTime
  apply hQ.mono'
    (((hS.isSemimartingale hF).adapted_continuousQuadraticVariation hF t).mono
      (F.le t) le_rfl).aestronglyMeasurable
  filter_upwards [hM.stopped_continuousQuadraticVariation_ae_le hF τ t] with ω hω
  have hS0 : 0 ≤ (hS.isSemimartingale hF).continuousQuadraticVariation hF t ω := by
    rw [← (hS.isSemimartingale hF).continuousQuadraticVariation_zero hF ω]
    exact (hS.isSemimartingale hF).monotone_continuousQuadraticVariation hF ω bot_le
  have hQ0 : 0 ≤ hM.klenkeSquareVariation hF (τ ω) ω := by
    rw [← hM.klenkeSquareVariation_zero hF ω]
    exact hM.monotone_klenkeSquareVariation hF ω bot_le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hS0, abs_of_nonneg hQ0] using hω

/-- The `L²` clause of Klenke 21.75.  The initial `L²` hypothesis is explicit:
the normalized bracket alone cannot control a non-`L²` time-zero variable. -/
theorem IsContinuousLocalMartingale.squareIntegrable_stoppedProcess_of_integrable_klenkeSquareVariation
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : MemLp (M 0) 2 P) (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P) :
    IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess M τ.withTop) F P := by
  let hS := hM.stoppedProcess hF τ.isStoppingTime
  apply (hS.squareIntegrable_iff_initial_and_continuousBracket_integrable hF).2
  have hinit : MemLp (MeasureTheory.stoppedProcess M τ.withTop 0) 2 P :=
    MemLp.ae_eq (ae_of_all P fun ω ↦ (stoppedProcess_eq_of_le bot_le).symm) h0
  refine ⟨hinit, ?_⟩
  exact hM.integrable_stopped_continuousQuadraticVariation hF τ hQ

/-- Quantitative `L²`-bounded form of the second clause of Klenke 21.75. -/
theorem IsContinuousLocalMartingale.squareIntegrable_stoppedProcess_and_secondMoment_le
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : MemLp (M 0) 2 P) (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P) :
    IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess M τ.withTop) F P ∧
      ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess M τ.withTop t ω ^ 2 ∂P) ≤
          (∫ ω, M 0 ω ^ 2 ∂P) +
            ∫ ω, hM.klenkeSquareVariation hF (τ ω) ω ∂P := by
  let hS := hM.stoppedProcess hF τ.isStoppingTime
  have hL := hM.squareIntegrable_stoppedProcess_of_integrable_klenkeSquareVariation
    hF h0 τ hQ
  refine ⟨hL, fun t ↦ ?_⟩
  have hQi := hM.integrable_stopped_continuousQuadraticVariation hF τ hQ t
  have hQle := integral_mono_ae hQi hQ
    (hM.stopped_continuousQuadraticVariation_ae_le hF τ t)
  have hmom := (hS.isSemimartingale hF)
    |>.integral_continuousQuadraticVariation_eq_sub_secondMoments hF hS.2 hL t
  change
    (∫ ω, (hS.isSemimartingale hF).continuousQuadraticVariation hF t ω ∂P) =
      (∫ ω, MeasureTheory.stoppedProcess M τ.withTop t ω ^ 2 ∂P) -
        ∫ ω, MeasureTheory.stoppedProcess M τ.withTop 0 ω ^ 2 ∂P at hmom
  have hinitial :
      (∫ ω, MeasureTheory.stoppedProcess M τ.withTop 0 ω ^ 2 ∂P) =
        ∫ ω, M 0 ω ^ 2 ∂P := by
    congr 1
    funext ω
    simp [FiniteStoppingTime.stoppedProcess_eq]
  rw [hinitial] at hmom
  linarith only [hmom, hQle]

/-- Centered `L²`-bounded form of Klenke 21.75.  It has no moment assumption
on `M 0`; this is the step that permits the expectation clause to require only
`M 0 ∈ L¹`. -/
theorem IsContinuousLocalMartingale.centered_stoppedProcess_squareIntegrable_and_secondMoment_le
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P) :
    IsSquareIntegrableMartingale
        (MeasureTheory.stoppedProcess (fun t ω ↦ M t ω - M 0 ω) τ.withTop) F P ∧
      ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess
          (fun s ω ↦ M s ω - M 0 ω) τ.withTop t ω ^ 2 ∂P) ≤
          ∫ ω, hM.klenkeSquareVariation hF (τ ω) ω ∂P := by
  let hN := hM.sub_initial hF
  have hbr := hM.klenkeSquareVariation_sub_initial hF
  have hbrτ :
      (fun ω ↦ hN.klenkeSquareVariation hF (τ ω) ω) =ᵐ[P]
        fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω :=
    hbr.mono fun ω hω ↦ hω (τ ω)
  have hQN : Integrable (fun ω ↦ hN.klenkeSquareVariation hF (τ ω) ω) P :=
    hQ.congr hbrτ.symm
  have hN0 : MemLp ((fun t ω ↦ M t ω - M 0 ω) 0) 2 P := by
    simpa only [sub_self] using
      (MemLp.zero' (μ := P) (p := 2) : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 P)
  have hNB := hN.squareIntegrable_stoppedProcess_and_secondMoment_le hF hN0 τ hQN
  refine ⟨hNB.1, fun t ↦ (hNB.2 t).trans_eq ?_⟩
  simpa only [sub_self, pow_two, zero_mul, integral_zero, zero_add] using
    (integral_congr_ae hbrτ)

/-- The expectation clause of Klenke 21.75 with the guard required by this
library's local-martingale semantics.  `M 0 ∈ L¹` is strictly weaker than the
`L²` premise used by the stopped-process clause above. -/
theorem IsContinuousLocalMartingale.integrable_finiteStoppingTime_value_and_integral_eq_initial
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : Integrable (M 0) P) (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P) :
    Integrable (fun ω ↦ M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ M t ω - M 0 ω
  let Y : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess N τ.withTop
  let hN := hM.sub_initial hF
  let hY := hN.stoppedProcess hF τ.isStoppingTime
  have hcenter := hM.centered_stoppedProcess_squareIntegrable_and_secondMoment_le hF τ hQ
  let C : ℝ≥0 := ⟨∫ ω, hM.klenkeSquareVariation hF (τ ω) ω ∂P,
    integral_nonneg fun ω ↦ by
      show (0 : ℝ) ≤ hM.klenkeSquareVariation hF (τ ω) ω
      calc
        (0 : ℝ) = hM.klenkeSquareVariation hF 0 ω :=
          (hM.klenkeSquareVariation_zero hF ω).symm
        _ ≤ hM.klenkeSquareVariation hF (τ ω) ω :=
          hM.monotone_klenkeSquareVariation hF ω bot_le⟩
  have hUI : UniformIntegrable Y 1 P := by
    apply uniformIntegrable_of_bounded_integral_sq hcenter.1.2 C
    intro t
    exact hcenter.2 t
  have hfinite : ∀ᵐ ω ∂P, τ.withTop ω ≠ ⊤ :=
    ae_of_all P τ.withTop_ne_top
  have hterminalUI : UniformIntegrable
      (fun _ : Unit ↦ stoppedValue Y τ.withTop) 1 P :=
    hcenter.1.1.uniformIntegrable_stoppedValue_of_ae_finite_usual hUI hF
      hY.2.hasRightContinuousPaths (fun _ ↦ τ.isStoppingTime) (fun _ ↦ hfinite)
  have hterminal : stoppedValue Y τ.withTop = fun ω ↦ M (τ ω) ω - M 0 ω := by
    simp only [Y, FiniteStoppingTime.stoppedValue_eq,
      FiniteStoppingTime.stoppedProcess_eq, min_self, N]
  have hdiff : Integrable (fun ω ↦ M (τ ω) ω - M 0 ω) P :=
    memLp_one_iff_integrable.mp ((hterminalUI.memLp ()).ae_eq (ae_of_all P fun ω ↦
      congrFun hterminal ω))
  have hτint : Integrable (fun ω ↦ M (τ ω) ω) P := by
    apply (hdiff.add h0).congr
    filter_upwards with ω
    simp only [Pi.add_apply]
    ring
  refine ⟨hτint, ?_⟩
  let ρ := FiniteStoppingTime.const F 0
  have hsample := hcenter.1.1.stoppedValue_ae_eq_condExp_of_ae_finite_usual hUI hF
    hY.2.hasRightContinuousPaths ρ.isStoppingTime τ.isStoppingTime
      (ae_of_all P fun _ ↦ bot_le) hfinite
  have hmean :
      (∫ ω, stoppedValue Y ρ.withTop ω ∂P) =
        ∫ ω, stoppedValue Y τ.withTop ω ∂P := by
    calc
      _ = ∫ ω, P[stoppedValue Y τ.withTop | ρ.measurableSpace] ω ∂P :=
        integral_congr_ae hsample
      _ = _ := integral_condExp ρ.measurableSpace_le
  have hinitial : stoppedValue Y ρ.withTop = fun _ ↦ 0 := by
    funext ω
    simp [ρ, Y, N, FiniteStoppingTime.stoppedValue_eq,
      FiniteStoppingTime.stoppedProcess_eq]
  have hcenterMean : (∫ ω, M (τ ω) ω - M 0 ω ∂P) = 0 := by
    calc
      _ = ∫ ω, stoppedValue Y τ.withTop ω ∂P := by rw [hterminal]
      _ = ∫ ω, stoppedValue Y ρ.withTop ω ∂P := hmean.symm
      _ = 0 := by rw [hinitial, integral_zero]
  have hsub := integral_sub hτint h0
  calc
    (∫ ω, M (τ ω) ω ∂P) =
        ((∫ ω, M (τ ω) ω ∂P) - ∫ ω, M 0 ω ∂P) + ∫ ω, M 0 ω ∂P := by ring
    _ = (∫ ω, M (τ ω) ω - M 0 ω ∂P) + ∫ ω, M 0 ω ∂P := by rw [hsub]
    _ = ∫ ω, M 0 ω ∂P := by rw [hcenterMean, zero_add]

/-- Klenke Theorem 21.75 in the finite stopping-time formulation.  The
expectation statement is also available above under the weaker assumption
`Integrable (M 0) P`; this bundled source-facing statement uses `M 0 ∈ L²`
because that is exactly the additional guard for the `L²`-bounded conclusion. -/
theorem IsContinuousLocalMartingale.klenke_21_75
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : MemLp (M 0) 2 P) (τ : FiniteStoppingTime F)
    (hQ : Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω) ω) P) :
    Integrable (fun ω ↦ M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P ∧
      IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess M τ.withTop) F P ∧
      ∀ t : ℝ≥0,
        (∫ ω, MeasureTheory.stoppedProcess M τ.withTop t ω ^ 2 ∂P) ≤
          (∫ ω, M 0 ω ^ 2 ∂P) +
            ∫ ω, hM.klenkeSquareVariation hF (τ ω) ω ∂P := by
  have hmean := hM.integrable_finiteStoppingTime_value_and_integral_eq_initial
    hF (h0.integrable one_le_two) τ hQ
  have hL2 := hM.squareIntegrable_stoppedProcess_and_secondMoment_le hF h0 τ hQ
  exact ⟨hmean.1, hmean.2, hL2.1, hL2.2⟩

/-- Klenke Corollary 21.76, stated with the normalized continuous bracket and
the necessary independent `L²` guard at time zero. -/
theorem IsContinuousLocalMartingale.klenke_21_76
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : MemLp (M 0) 2 P)
    (hQ : ∀ t : ℝ≥0, Integrable (hM.klenkeSquareVariation hF t) P) :
    IsSquareIntegrableMartingale M F P :=
  (hM.squareIntegrable_iff_initial_and_continuousBracket_integrable hF).2 ⟨h0, hQ⟩

end ProbabilityTheory
