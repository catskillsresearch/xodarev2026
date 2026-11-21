/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.PredictableJumpIntegrableMultiplier
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUITerminal

/-! # Integrable predictable jump multipliers with possibly infinite lifetime

UI optional sampling at the actual announcing times and the native before-field
identity identify the stopped left limit with conditional expectation. At an
infinite lifetime both stopped terms use the same actual martingale terminal
limit, so their difference has terminal value zero. Finite evaluations of
announcing times are used only after strict announcing and positive lifetime
have proved them finite.

The resulting zero-terminal jump has zero conditional mean, including on the
infinite-lifetime event. A bounded cadlag martingale supplies the common `2 * C`
jump bound; hence every integrable before-field coefficient can be pulled out.
There is no boundedness or L2 premise on that coefficient and no transfer of its
measurability to an unproved truncated before-field. Positive lifetime remains
explicit because the source initial jump is the initial value.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
  {Z K : Ω → ℝ}

/-- UI optional sampling and the announcing limit give the before-field identity
with the actual terminal value on both sides when the lifetime is infinite. -/
theorem stopped_leftLimitWithTerminal_ae_eq_condExp_before_of_predictable
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ M t ω) atTop (𝓝 (Z ω))) :
    stoppedValueWithTerminal (leftLimitProcess M) Z τ =ᵐ[P]
      P[stoppedValueWithTerminal M Z τ | hτ.1.measurableSpaceBefore] := by
  obtain ⟨σ, hs, hle⟩ := hτ.exists_announcing_le
  have hmono : Monotone σ := fun _ _ hnm ω ↦ hs.monotone ω hnm
  let G : Filtration ℕ mΩ := F.stoppingTimeReindex σ hs.isStoppingTime hmono
  have heG : hτ.1.measurableSpaceBefore = ⨆ n, G n :=
    hs.measurableSpaceBefore_eq_iSup hτ.1 hF.complete_initial
  have he (n : ℕ) : stoppedValue M (σ n) =ᵐ[P]
      P[stoppedValueWithTerminal M Z τ | G n] := by
    have hsample := hM.stoppedValueWithTerminal_ae_eq_condExp_of_ae_le
      hu hF hc.hasRightContinuousPaths hlim (hs.isStoppingTime n) hτ.1
      (Eventually.of_forall (hle n))
    filter_upwards [hpos, hsample] with ω hp hh
    have hf : σ n ω ≠ ⊤ := ne_top_of_lt ((hs.strict n ω hp).trans_le le_top)
    rwa [stoppedValueWithTerminal_of_ne_top hf] at hh
  have hCE : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ P[stoppedValueWithTerminal M Z τ | G n] ω) atTop
      (𝓝 (P[stoppedValueWithTerminal M Z τ | hτ.1.measurableSpaceBefore] ω)) := by
    rw [heG]
    exact tendsto_ae_condExp (ℱ := G) (μ := P) (stoppedValueWithTerminal M Z τ)
  filter_upwards [hc, hpos, hlim, hs.tendsto, ae_all_iff.mpr he, hCE]
    with ω hcω hpω hlω hsω heω hCEω
  have hσfinite (n : ℕ) : σ n ω ≠ ⊤ :=
    ne_top_of_lt ((hs.strict n ω hpω).trans_le le_top)
  have hleft : Tendsto (fun n ↦ stoppedValue M (σ n) ω) atTop
      (𝓝 (stoppedValueWithTerminal (leftLimitProcess M) Z τ ω)) := by
    by_cases ht : τ ω = ⊤
    · rw [stoppedValueWithTerminal_of_top ht]
      have htop : Tendsto (fun n ↦ σ n ω) atTop (𝓝 ⊤) := by
        simpa only [ht] using hsω
      have htime : Tendsto (fun n ↦ (σ n ω).untopA) atTop atTop := by
        apply tendsto_atTop.mpr
        intro t
        filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp htop t] with n hn
        lift σ n ω to ℝ≥0 using hσfinite n with s hsval
        exact (WithTop.coe_lt_coe.mp hn).le
      exact hlω.comp htime
    · rw [stoppedValueWithTerminal_of_ne_top ht]
      have hp : 0 < (τ ω).untopA := by
        have h := hpω
        lift τ ω to ℝ≥0 using ht with t htval
        exact WithTop.coe_lt_coe.mp h
      have hlt (n : ℕ) : (σ n ω).untopA < (τ ω).untopA := by
        have h := hs.strict n ω hpω
        lift σ n ω to ℝ≥0 using hσfinite n with s hsval
        lift τ ω to ℝ≥0 using ht with t htval
        exact WithTop.coe_lt_coe.mp h
      have htime : Tendsto (fun n ↦ (σ n ω).untopA) atTop (𝓝[<] (τ ω).untopA) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨(WithTop.tendsto_untopA ht).comp hsω, Eventually.of_forall hlt⟩
      exact (hcω.tendsto_leftLimitProcess (ne_of_gt hp)).comp htime
  exact tendsto_nhds_unique hleft (hCEω.congr fun n ↦ (heω n).symm)

/-- A UI cadlag martingale has an integrable, zero-conditional-mean jump at a
positive predictable lifetime, using the explicit zero terminal at infinity.
The actual martingale terminal is constructed, not supplied as a hypothesis. -/
theorem integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ) P ∧
      P[stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ |
        hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  obtain ⟨Z, _, hlim, _, _⟩ :=
    hM.exists_integrable_limit_of_uniformIntegrable hc.hasRightContinuousPaths hu
  let V := stoppedValueWithTerminal M Z τ
  let L := stoppedValueWithTerminal (leftLimitProcess M) Z τ
  have hiV : Integrable V P :=
    hM.integrable_stoppedValueWithTerminal hu hF hc.hasRightContinuousPaths hlim hτ.1
  have heL : L =ᵐ[P] P[V | hτ.1.measurableSpaceBefore] :=
    hM.stopped_leftLimitWithTerminal_ae_eq_condExp_before_of_predictable hu hF hc hτ hpos hlim
  have hiL : Integrable L P := integrable_condExp.congr heL.symm
  have heJ : stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ = V - L := by
    funext ω
    by_cases ht : τ ω = ⊤
    · simp only [V, L, stoppedValueWithTerminal_of_top ht, Pi.sub_apply, sub_self]
    · simp only [V, L, stoppedValueWithTerminal_of_ne_top ht, Pi.sub_apply]
      rfl
  rw [heJ]
  refine ⟨hiV.sub hiL, ?_⟩
  have hce : P[L | hτ.1.measurableSpaceBefore] =ᵐ[P]
      P[V | hτ.1.measurableSpaceBefore] :=
    (condExp_congr_ae heL).trans
      (condExp_condExp_of_le le_rfl hτ.1.measurableSpaceBefore_le_ambient)
  filter_upwards [condExp_sub hiV hiL hτ.1.measurableSpaceBefore, hce] with ω hlin hω
  change _ = (0 : ℝ)
  rw [hlin]
  change P[V | hτ.1.measurableSpaceBefore] ω -
    P[L | hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, sub_self]

/-- The zero-terminal jump bound gives product integrability for an arbitrary
integrable coefficient, with no finite-lifetime or coefficient bound premise. -/
theorem integrable_mul_stopped_jumpWithTerminal_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hiK : Integrable K P) :
    Integrable (K * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ) P := by
  have hu : UniformIntegrable M 1 P :=
    ((hM.isLocalMartingale hc).isUIMartingale_of_bound ⟨C, hC⟩ hb).2
  have hiJ :=
    (hM.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
      hu hF hc hτ hpos).1
  apply (hiK.norm.const_mul (2 * C)).mono'
    (hiK.aestronglyMeasurable.mul hiJ.aestronglyMeasurable)
  filter_upwards [hc.ae_forall_norm_stopped_jump_le_of_bound hb (fun _ : Unit ↦ τ)]
    with ω hω
  change ‖K ω * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω‖ ≤
    2 * C * ‖K ω‖
  rw [norm_mul, mul_comm (2 * C)]
  exact mul_le_mul_of_nonneg_left (hω ()) (norm_nonneg _)

/-- Pull-out for an integrable coefficient in the original before-field gives
zero conditional mean with the explicit zero terminal at infinity. -/
theorem condExp_mul_stopped_jumpWithTerminal_before_ae_eq_zero_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K) (hiK : Integrable K P) :
    P[K * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ |
      hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  have hu : UniformIntegrable M 1 P :=
    ((hM.isLocalMartingale hc).isUIMartingale_of_bound ⟨C, hC⟩ hb).2
  obtain ⟨hiJ, hz⟩ :=
    hM.integrable_stopped_jumpWithTerminal_and_condExp_before_ae_eq_zero_of_predictable
      hu hF hc hτ hpos
  have hip := hM.integrable_mul_stopped_jumpWithTerminal_of_integrable_of_bounded_martingale
    hF hc C hC hb hτ hpos hiK
  have hout := condExp_mul_of_stronglyMeasurable_left hK hip hiJ
  filter_upwards [hout, hz] with ω hp hω
  change _ = (0 : ℝ)
  rw [hp]
  change K ω * P[stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ |
    hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, Pi.zero_apply, mul_zero]

/-- The actual integrable weighted zero-terminal jump has expectation zero. -/
theorem integral_mul_stopped_jumpWithTerminal_eq_zero_of_integrable_of_bounded_martingale
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K) (hiK : Integrable K P) :
    (∫ ω, K ω * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω ∂P) = 0 := by
  have hz :=
    hM.condExp_mul_stopped_jumpWithTerminal_before_ae_eq_zero_of_integrable_of_bounded_martingale
      hF hc C hC hb hτ hpos hK hiK
  calc
    (∫ ω, K ω * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω ∂P) =
        ∫ ω, P[K * stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ |
          hτ.1.measurableSpaceBefore] ω ∂P :=
      (integral_condExp hτ.1.measurableSpaceBefore_le_ambient).symm
    _ = 0 := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hz

end MeasureTheory.Martingale
