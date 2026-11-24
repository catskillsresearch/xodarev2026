module

public import SignatureVolatility.ItoCalculusKit.StoppedStep

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SignatureVolatility

/-!
# The weighted energy step for the kit processes

Moment inputs for `weighted_step_le` from the signature volatility (H1–H2): fourth moments of
`ΔQ = ∫_u^v σ²` and the `L²` freezing error `ΔQ - (v - u) σ_u²`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section SigmaMoments

variable {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
  {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)

include hw hℓ in
lemma measurable_quadIncr {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    Measurable fun ω => ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2 := by
  have : (fun ω => ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) =
      fun ω => ∫ s in u..v, sigmaExt B hT ℓ s ω ^ 2 :=
    funext fun ω => intervalIntegral_sigma_eq_sigmaExt hu huv hvT 2 ω
  rw [this]
  exact measurable_intervalIntegral_sigmaExt hw hℓ huv 2

include hw hℓ in
/-- Fourth moments of `ΔQ = ∫_u^v σ²`. -/
theorem quadIncr_pow_four_le : ∃ cQ, 0 ≤ cQ ∧ ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
    MemLp (fun ω => ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) 4 P ∧
    ∫ ω, (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 4 ∂P ≤ cQ * (v - u) ^ 4 := by
  obtain ⟨M, hM, h8⟩ := integral_quadIncr_pow_eight_le (B := B) (hT := hT) hw hℓ
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun u v hu huv hvT => ?_⟩
  obtain ⟨hi8, hb8⟩ := h8 u v hu huv hvT
  set X : Ω → ℝ := fun ω => ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2 with hX
  have hXm : Measurable X := measurable_quadIncr B hT hw hℓ hu huv hvT
  have hi4 : Integrable (fun ω => X ω ^ 4) P := by
    refine Integrable.mono' ((integrable_const 1).add hi8) (hXm.pow_const 4).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X ω ^ 4 - 1), pow_two_nonneg (X ω ^ 4)]
  have hL4 : MemLp X 4 P := memLp_four_of_integrable_pow_four hXm.aestronglyMeasurable hi4
  have hL4' : MemLp (fun ω => X ω ^ 2) 4 P :=
    memLp_four_of_integrable_pow_four (hXm.pow_const 2).aestronglyMeasurable
      (hi8.congr (ae_of_all _ fun ω => by simp only [hX]; ring))
  refine ⟨hL4, ?_⟩
  have j := sq_integral_sq_le_integral_pow_four hL4'
  have e1 : ∫ ω, (X ω ^ 2) ^ 2 ∂P = ∫ ω, X ω ^ 4 ∂P := by congr 1; funext ω; ring
  have e2 : ∫ ω, (X ω ^ 2) ^ 4 ∂P = ∫ ω, X ω ^ 8 ∂P := by congr 1; funext ω; ring
  rw [e1, e2] at j
  have h1 : ∫ ω, X ω ^ 4 ∂P ≤ Real.sqrt (∫ ω, X ω ^ 8 ∂P) :=
    (le_abs_self _).trans (Real.abs_le_sqrt j)
  refine h1.trans ?_
  calc Real.sqrt (∫ ω, X ω ^ 8 ∂P) ≤ Real.sqrt (M * ((v - u) ^ 4) ^ 2) :=
        Real.sqrt_le_sqrt (hb8.trans_eq (by ring))
    _ = Real.sqrt M * (v - u) ^ 4 := by
        rw [Real.sqrt_mul hM, Real.sqrt_sq (by have := sub_nonneg.mpr huv; positivity)]

include hw hℓ in
/-- `E (σ_r² - σ_u²)² ≤ c (r - u)`. -/
theorem sigma_sq_sub_sq_le : ∃ cS, 0 ≤ cS ∧ ∀ u r, 0 ≤ u → u ≤ r → r ≤ T →
    ∫ ω, (signatureSigma B hT ℓ r ω ^ 2 - signatureSigma B hT ℓ u ω ^ 2) ^ 2 ∂P ≤
      cS * (r - u) := by
  obtain ⟨K, hK⟩ := holderAdapted_signatureSigma B hT hw hℓ T
  set σ := signatureSigma B hT ℓ with hσ
  set Mσ : ℝ := 8 * ∫ ω, σ 0 ω ^ 4 ∂P + 8 * K * T ^ 2 with hMσ
  have hMσ0 : 0 ≤ Mσ := by
    have : 0 ≤ ∫ ω, σ 0 ω ^ 4 ∂P := integral_nonneg fun ω => by positivity
    have := hK.K_nonneg
    positivity
  refine ⟨Real.sqrt K * (4 * Real.sqrt Mσ), by positivity, fun u r hu hur hrT => ?_⟩
  have huT : u ≤ T := hur.trans hrT
  have hr0 : 0 ≤ r := hu.trans hur
  have hσu := hK.memLp u hu huT
  have hσr := hK.memLp r hr0 hrT
  have hcs := integral_sq_mul_sq_le (hσr.sub hσu) (hσr.add hσu)
  have e : ∫ ω, (σ r ω ^ 2 - σ u ω ^ 2) ^ 2 ∂P =
      ∫ ω, (σ r - σ u) ω ^ 2 * (σ r + σ u) ω ^ 2 ∂P := by
    congr 1; funext ω; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [e]
  refine hcs.trans ?_
  have h1 : Real.sqrt (∫ ω, (σ r - σ u) ω ^ 4 ∂P) ≤ Real.sqrt K * (r - u) := by
    calc Real.sqrt (∫ ω, (σ r - σ u) ω ^ 4 ∂P) ≤ Real.sqrt (K * (r - u) ^ 2) :=
          Real.sqrt_le_sqrt (hK.holder u r hu hur hrT)
      _ = Real.sqrt K * (r - u) := by
          rw [Real.sqrt_mul hK.K_nonneg, Real.sqrt_sq (sub_nonneg.mpr hur)]
  have h2 : Real.sqrt (∫ ω, (σ r + σ u) ω ^ 4 ∂P) ≤ 4 * Real.sqrt Mσ := by
    have j1 := integrable_pow_of_memLp_four hσr (k := 4) le_rfl
    have j2 := integrable_pow_of_memLp_four hσu (k := 4) le_rfl
    have b1 := integral_pow_four_le_of_holderAdapted B hK hr0 hrT
    have b2 := integral_pow_four_le_of_holderAdapted B hK hu huT
    have hS : ∫ ω, (σ r + σ u) ω ^ 4 ∂P ≤ 16 * Mσ := by
      calc ∫ ω, (σ r + σ u) ω ^ 4 ∂P ≤ ∫ ω, (8 * σ r ω ^ 4 + 8 * σ u ω ^ 4) ∂P :=
            integral_mono (integrable_pow_of_memLp_four (hσr.add hσu) (k := 4) le_rfl)
              ((j1.const_mul 8).add (j2.const_mul 8)) fun ω => add_pow_four_le_frozen _ _
        _ = 8 * ∫ ω, σ r ω ^ 4 ∂P + 8 * ∫ ω, σ u ω ^ 4 ∂P := by
            rw [integral_add (j1.const_mul 8) (j2.const_mul 8), integral_const_mul,
              integral_const_mul]
        _ ≤ 16 * Mσ := by rw [hMσ]; linarith
    calc Real.sqrt (∫ ω, (σ r + σ u) ω ^ 4 ∂P) ≤ Real.sqrt (16 * Mσ) := Real.sqrt_le_sqrt hS
      _ = 4 * Real.sqrt Mσ := by
          rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  calc Real.sqrt (∫ ω, (σ r - σ u) ω ^ 4 ∂P) * Real.sqrt (∫ ω, (σ r + σ u) ω ^ 4 ∂P)
      ≤ (Real.sqrt K * (r - u)) * (4 * Real.sqrt Mσ) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

include hw hℓ in
/-- **Freezing error of `ΔQ`**: `E (∫_u^v σ² - (v - u) σ_u²)² ≤ c (v - u)³`. -/
theorem quadIncr_sub_frozen_sq_le : ∃ cE, 0 ≤ cE ∧ ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
    ∫ ω, ((∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) -
      (v - u) * signatureSigma B hT ℓ u ω ^ 2) ^ 2 ∂P ≤ cE * (v - u) ^ 3 := by
  obtain ⟨cS, hcS, hS⟩ := sigma_sq_sub_sq_le B hT hw hℓ
  refine ⟨cS, hcS, fun u v hu huv hvT => ?_⟩
  set σ := signatureSigma B hT ℓ with hσ
  have huT : u ≤ T := huv.trans hvT
  obtain ⟨f, hfm, hfc, hfe⟩ : ∃ f : ℝ → Ω → ℝ, Measurable (Function.uncurry f) ∧
      (∀ ω, Continuous fun r => f r ω) ∧ ∀ r ∈ Icc 0 T, ∀ ω, f r ω = σ r ω :=
    ⟨sigmaExt B hT ℓ, measurable_uncurry_sigmaExt hw hℓ, fun ω => continuous_sigmaExt hw hℓ ω,
      fun r hr ω => sigmaExt_of_mem B hT ℓ hr ω⟩
  set Y : Ω → ℝ := fun ω => ∫ r in u..v, (f r ω ^ 2 - f u ω ^ 2) ^ 2 with hY
  have hcont : ∀ ω, Continuous fun r => (f r ω ^ 2 - f u ω ^ 2) ^ 2 := fun ω =>
    (((hfc ω).pow 2).sub continuous_const).pow 2
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω =>
    intervalIntegral.integral_nonneg huv fun r _ => sq_nonneg _
  have hjm : Measurable (Function.uncurry fun (ω : Ω) (r : ℝ) => (f r ω ^ 2 - f u ω ^ 2) ^ 2) := by
    have h1 : Measurable (fun p : Ω × ℝ => f p.2 p.1) :=
      hfm.comp measurable_swap
    have hg : Measurable (f u) := hfm.of_uncurry_left
    have h2 : Measurable (fun p : Ω × ℝ => f u p.1) :=
      hg.comp measurable_fst
    exact ((h1.pow_const 2).sub (h2.pow_const 2)).pow_const 2
  have hYm : Measurable Y := by
    have h := hjm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc u v))
    simp only [hY, intervalIntegral.integral_of_le huv]
    exact h.measurable
  have hstep1 : ∀ ω, ENNReal.ofReal (Y ω) =
      ∫⁻ r in Ioc u v, ENNReal.ofReal ((f r ω ^ 2 - f u ω ^ 2) ^ 2) := by
    intro ω
    simp only [hY]
    rw [intervalIntegral.integral_of_le huv]
    exact ofReal_integral_eq_lintegral_ofReal
      (((hcont ω).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun r => by positivity)
  have hm : Measurable (Function.uncurry fun (ω : Ω) (r : ℝ) =>
      ENNReal.ofReal ((f r ω ^ 2 - f u ω ^ 2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp hjm
  have hcv : 0 ≤ cS * (v - u) := mul_nonneg hcS (sub_nonneg.mpr huv)
  have hlint : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤ ENNReal.ofReal (cS * (v - u) * (v - u)) := by
    calc ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P
        = ∫⁻ ω, (∫⁻ r in Ioc u v, ENNReal.ofReal ((f r ω ^ 2 - f u ω ^ 2) ^ 2)) ∂P :=
          lintegral_congr hstep1
      _ = ∫⁻ r in Ioc u v, ∫⁻ ω, ENNReal.ofReal ((f r ω ^ 2 - f u ω ^ 2) ^ 2) ∂P :=
          lintegral_lintegral_swap hm.aemeasurable
      _ ≤ ∫⁻ r in Ioc u v, ENNReal.ofReal (cS * (v - u)) := by
          refine setLIntegral_mono measurable_const fun r hr => ?_
          have hr' : r ∈ Icc 0 T := ⟨hu.trans hr.1.le, hr.2.trans hvT⟩
          have hu' : u ∈ Icc 0 T := ⟨hu, huT⟩
          have hfun : (fun ω => ENNReal.ofReal ((f r ω ^ 2 - f u ω ^ 2) ^ 2)) =
              fun ω => ENNReal.ofReal ((σ r ω ^ 2 - σ u ω ^ 2) ^ 2) := by
            funext ω; rw [hfe r hr' ω, hfe u hu' ω]
          obtain ⟨K, hK⟩ := holderAdapted_signatureSigma B hT hw hℓ T
          have hi : Integrable (fun ω => (σ r ω ^ 2 - σ u ω ^ 2) ^ 2) P := by
            have := integrable_pow_mul_pow_of_memLp_four ((hK.memLp r hr'.1 hr'.2).sub
              (hK.memLp u hu huT)) ((hK.memLp r hr'.1 hr'.2).add (hK.memLp u hu huT))
              (p := 2) (q := 2) rfl
            refine this.congr (ae_of_all _ fun ω => ?_)
            simp only [Pi.sub_apply, Pi.add_apply]; ring
          rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun ω => by positivity)]
          refine ENNReal.ofReal_le_ofReal (((hS u r hu hr.1.le (hr.2.trans hvT)).trans ?_))
          exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) hcS
      _ = ENNReal.ofReal (cS * (v - u) * (v - u)) := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hcv]
  have hYi : Integrable Y P := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) (hlint.trans_lt ENNReal.ofReal_lt_top)
    rw [Real.enorm_eq_ofReal (hY0 ω)]
  have hYle : ∫ ω, Y ω ∂P ≤ cS * (v - u) * (v - u) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcv (sub_nonneg.mpr huv)),
      ofReal_integral_eq_lintegral_ofReal hYi (ae_of_all _ hY0)]
    exact hlint
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ ω, ((∫ s in u..v, σ s ω ^ 2) - (v - u) * σ u ω ^ 2) ^ 2 ≤ (v - u) * Y ω := by
    intro ω
    have hc : ContinuousOn (fun r => f r ω ^ 2 - f u ω ^ 2) (Icc u v) :=
      (((hfc ω).pow 2).sub continuous_const).continuousOn
    have hcs := sq_intervalIntegral_le huv hc
    have hc2 : Continuous fun r => f r ω ^ 2 := (hfc ω).pow 2
    have h1 : ∫ s in u..v, σ s ω ^ 2 = ∫ r in u..v, f r ω ^ 2 :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le huv] at hr
        simp only [hfe r ⟨hu.trans hr.1, hr.2.trans hvT⟩ ω]
    have e : (∫ s in u..v, σ s ω ^ 2) - (v - u) * σ u ω ^ 2 =
        ∫ r in u..v, (f r ω ^ 2 - f u ω ^ 2) := by
      rw [intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, h1, hfe u ⟨hu, huT⟩ ω]
    rw [e]
    exact hcs
  have hvu0 : 0 ≤ v - u := sub_nonneg.mpr huv
  calc ∫ ω, ((∫ s in u..v, σ s ω ^ 2) - (v - u) * σ u ω ^ 2) ^ 2 ∂P
      ≤ ∫ ω, (v - u) * Y ω ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (hYi.const_mul _)
          (ae_of_all _ hpt)
    _ = (v - u) * ∫ ω, Y ω ∂P := integral_const_mul _ _
    _ ≤ (v - u) * (cS * (v - u) * (v - u)) := mul_le_mul_of_nonneg_left hYle hvu0
    _ = cS * (v - u) ^ 3 := by ring

end SigmaMoments

/-- Weighted energy `Φ(t) = E[I_t² e^{-∫₀ᵗ σ²}]` of the raw integral of `G`. -/
noncomputable def kitEnergy {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) (G : ℝ → Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, kitItoIntRaw B G t ω ^ 2 * Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) t ω) ∂P

section KitStep

variable {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
  {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)

include hd hw hℓ in
/-- **One step of the weighted energy for the kit processes.** -/
theorem kitEnergy_step {G : ℝ → Ω → ℝ} {K : ℝ} (hG : HolderAdapted B G T K)
    (hGs : ∀ u ∈ Icc 0 T, ∀ᵐ ω ∂P,
      G u ω ^ 2 = kitItoIntRaw B G u ω ^ 2 * signatureSigma B hT ℓ u ω ^ 2) :
    ∃ C₃ C₄ : ℝ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      kitEnergy B hT ℓ G v - kitEnergy B hT ℓ G u ≤
        C₃ * Real.sqrt (v - u) ^ 3 + C₄ * Real.sqrt (v - u) ^ 4 := by
  obtain ⟨cQ, hcQ, hQb⟩ := quadIncr_pow_four_le B hT hw hℓ
  obtain ⟨cE, hcE, hEb⟩ := quadIncr_sub_frozen_sq_le B hT hw hℓ
  obtain ⟨Kσ, hKσ⟩ := holderAdapted_signatureSigma B hT hw hℓ T
  set c4 : ℝ := gaussFourthConst with hc4
  have hc40 : 0 ≤ c4 := gaussFourthConst_nonneg
  have hK0 := hG.K_nonneg
  set M4 : ℝ := 8 * ∫ ω, G 0 ω ^ 4 ∂P + 8 * K * T ^ 2 with hM4
  have hM40 : 0 ≤ M4 := by
    have : 0 ≤ ∫ ω, G 0 ω ^ 4 ∂P := integral_nonneg fun ω => by positivity
    positivity
  set cI : ℝ := 16 * c4 * M4 with hcI
  have hcI0 : 0 ≤ cI := by positivity
  set M : ℝ := cI * T ^ 2 + M4 with hM
  have hM0 : 0 ≤ M := by positivity
  set cR : ℝ := 128 * c4 * K with hcR
  have hcR0 : 0 ≤ cR := by positivity
  refine ⟨2 * (Real.sqrt (Real.sqrt M * Real.sqrt c4) * Real.sqrt (Real.sqrt cR)) +
          Real.sqrt (Real.sqrt cI) * Real.sqrt (4 * Real.sqrt M * Real.sqrt cQ) +
          Real.sqrt M * Real.sqrt cE,
    Real.sqrt cR + Real.sqrt M * Real.sqrt cQ, fun u v hu huv hvT => ?_⟩
  have huT : u ≤ T := huv.trans hvT
  have hv0 : 0 ≤ v := hu.trans huv
  set k := kitDriver hd with hk
  set s : ℝ := Real.sqrt (v - u) with hsdef
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = v - u := Real.sq_sqrt (sub_nonneg.mpr huv)
  -- the weight
  set a : Ω → ℝ := fun ω => Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) u ω) with ha
  have hQf : ∀ t ∈ Icc 0 T, ∀ ω, kitQuadVarRaw B (signatureSigma B hT ℓ) t ω =
      ∫ r in (0 : ℝ)..t, signatureSigma B hT ℓ r ω ^ 2 :=
    fun t ht ω => kitQuadVarRaw_signatureSigma B hd hT w hw ℓ hℓ ht ω
  have hQf0 : ∀ ω, 0 ≤ kitQuadVarRaw B (signatureSigma B hT ℓ) u ω := fun ω => by
    rw [hQf u ⟨hu, huT⟩ ω]
    exact intervalIntegral.integral_nonneg hu fun r _ => sq_nonneg _
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => (Real.exp_pos _).le
  have ha1 : ∀ ω, a ω ≤ 1 := fun ω => by
    simp only [ha]; rw [Real.exp_le_one_iff]; linarith [hQf0 ω]
  have hamF : Measurable[(pathFiltration B).σAlg u] a :=
    Real.measurable_exp.comp (measurable_kitQuadVarRaw_path B (signatureSigma B hT ℓ) hu
      (fun r h0 hr => measurable_signatureSigma_path B hT ℓ u ⟨r, h0, hr⟩)).neg
  have ham : AEStronglyMeasurable a P :=
    (hamF.mono ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable
  -- the increments
  set ΔQ : Ω → ℝ := fun ω => ∫ r in u..v, signatureSigma B hT ℓ r ω ^ 2 with hΔQ
  have hsplit : ∀ ω, Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) v ω) =
      a ω * Real.exp (-ΔQ ω) := by
    intro ω
    have hc := ((continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).pow 2)
    have i1 : IntervalIntegrable (fun r => signatureSigma B hT ℓ r ω ^ 2) volume 0 u :=
      (hc.mono (Icc_subset_Icc_right huT)).intervalIntegrable_of_Icc hu
    have i2 : IntervalIntegrable (fun r => signatureSigma B hT ℓ r ω ^ 2) volume u v :=
      (hc.mono (Icc_subset_Icc hu hvT)).intervalIntegrable_of_Icc huv
    rw [hQf v ⟨hv0, hvT⟩ ω, ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
      neg_add, Real.exp_add]
    simp only [ha, hΔQ, hQf u ⟨hu, huT⟩ ω]
  have hIv := kitItoIntRaw_of_holderAdapted B hd hv0 (hG.mono hvT)
  have hIu := kitItoIntRaw_of_holderAdapted B hd hu (hG.mono huT)
  have hIuF : Measurable[(pathFiltration B).σAlg u] (kitItoIntRaw B G u) :=
    measurable_kitItoIntRaw_path B G hu (fun r h0 hr =>
      (hG.meas r h0 (hr.trans huT)).mono ((pathFiltration B).mono hr) le_rfl)
  have hGu := hG.memLp u hu huT
  have hGuF := hG.meas u hu huT
  have hWlaw := hasLaw_wnnIncr B k hu huv
  have hW : MemLp (fun ω => wnnIncr B k u v ω) 4 P :=
    hWlaw.memLp (memLp_id_gaussianReal' (μ := 0) 4 (by simp))
  have hGW := memLp_mul_wnnIncr B k hu huv hGuF hGu
  obtain ⟨hQL, hQ4⟩ := hQb u v hu huv hvT
  have hσu := hKσ.memLp u hu huT
  have hs2L : MemLp (fun ω => signatureSigma B hT ℓ u ω ^ 2) 2 P := memLp_sq_two_of_four hσu
  have hQ0 : ∀ ω, 0 ≤ ΔQ ω := fun ω =>
    intervalIntegral.integral_nonneg huv fun r _ => sq_nonneg _
  -- orthogonality
  have horth : ∫ ω, a ω * kitItoIntRaw B G u ω * (kitItoIntRaw B G v ω - kitItoIntRaw B G u ω) ∂P
      = 0 :=
    integral_mul_kitItoIntRaw_sub_eq_zero B hd hG hu huv hvT (hamF.mul hIuF)
      (memLp_bdd_mul ham ha0 ha1 (hIu.2.1.mono_exponent (by norm_num)))
  -- independence
  have hind : ∫ ω, a ω * G u ω ^ 2 * wnnIncr B k u v ω ^ 2 ∂P =
      s ^ 2 * ∫ ω, a ω * G u ω ^ 2 ∂P := by
    have hgF : Measurable[(pathFiltration B).σAlg u] (fun ω => a ω * G u ω ^ 2) :=
      hamF.mul (hGuF.pow_const 2)
    have hindep := (indepFun_pathFiltration_wnnIncr B k huv hgF).comp measurable_id
      (measurable_id.pow_const 2)
    have hX : AEStronglyMeasurable (fun ω => a ω * G u ω ^ 2) P :=
      (hgF.mono ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable
    have hY : AEStronglyMeasurable (fun ω => wnnIncr B k u v ω ^ 2) P :=
      ((measurable_wnnIncr B k u v).pow_const 2).aestronglyMeasurable
    have h1 := hindep.integral_fun_mul_eq_mul_integral hX hY
    have hW2i : Integrable (fun ω => wnnIncr B k u v ω ^ 2) P :=
      integrable_pow_of_memLp_four hW (k := 2) (by norm_num)
    have hW2 : ∫ ω, wnnIncr B k u v ω ^ 2 ∂P = v - u := by
      have h0 := integral_qvIncrR B k hu huv
      simp only [qvIncrR] at h0
      rw [integral_sub hW2i (integrable_const _), integral_const] at h0
      simp at h0
      linarith
    simp only [Function.comp_def, id] at h1
    rw [h1, hW2, hs2]
    ring
  -- remainder and increments
  obtain ⟨-, hR⟩ := integral_kitItoIntRaw_sub_frozen_pow_four_le B hd hG hu huv hvT
  obtain ⟨-, hdI⟩ := integral_kitItoIntRaw_sub_pow_four_le B hd hG hu huv hvT
  have hI4 : ∀ r, 0 ≤ r → r ≤ T → ∫ ω, kitItoIntRaw B G r ω ^ 4 ∂P ≤ M := by
    intro r hr hrT
    obtain ⟨-, h⟩ := integral_kitItoIntRaw_sub_pow_four_le B hd hG le_rfl hr hrT
    simp only [kitItoIntRaw_zero, sub_zero] at h
    have hr2 : (r - 0) ^ 2 ≤ T ^ 2 := by rw [sub_zero]; exact pow_le_pow_left₀ hr hrT 2
    have : cI * (r - 0) ^ 2 ≤ cI * T ^ 2 := mul_le_mul_of_nonneg_left hr2 hcI0
    rw [hM]; linarith
  have hG4 := integral_pow_four_le_of_holderAdapted B hG hu huT
  have hW4 : ∫ ω, wnnIncr B k u v ω ^ 4 ∂P ≤ c4 * s ^ 4 := by
    have h1 := hWlaw.integral_comp (f := fun x : ℝ => x ^ 4)
      (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable
    simp only [Function.comp_def] at h1
    rw [h1, integral_pow_four_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.mpr huv), ← hs2]
    apply le_of_eq; rw [hc4]; ring
  have hE := hEb u v hu huv hvT
  rw [← hs2] at hE
  have key := weighted_step_le (P := P) (a := a) (Iu := kitItoIntRaw B G u)
    (Iv := kitItoIntRaw B G v) (G := G u) (W := fun ω => wnnIncr B k u v ω) (Q := ΔQ)
    (s2 := fun ω => signatureSigma B hT ℓ u ω ^ 2) (s := s) (M := M) (cR := cR) (cI := cI)
    (cQ := cQ) (cE := cE) (cW := c4) hs hM0 hcR0 hcI0 hcQ hcE hc40 ha0 ha1 ham hIu.2.1 hIv.2.1
    hGu hW hGW hQL hs2L hQ0 horth hind (hGs u ⟨hu, huT⟩)
    (hR.trans_eq (by rw [hcR, ← hs2]; ring)) (hdI.trans_eq (by rw [hcI, ← hs2]; ring))
    (hI4 u hu huT) (hI4 v hv0 hvT) (hG4.trans (by rw [hM]; nlinarith)) hW4
    (hQ4.trans_eq (by rw [← hs2]; ring)) (hE.trans_eq (by ring))
  have hEv : kitEnergy B hT ℓ G v =
      ∫ ω, kitItoIntRaw B G v ω ^ 2 * (a ω * Real.exp (-ΔQ ω)) ∂P := by
    simp only [kitEnergy]
    congr 1; funext ω; rw [hsplit ω]
  have hEu : kitEnergy B hT ℓ G u = ∫ ω, kitItoIntRaw B G u ω ^ 2 * a ω ∂P := rfl
  rw [hEv, hEu]
  exact key

/-- **Grid summation**: a function vanishing at `0` whose increments are `O(h^{3/2})` is
nonpositive. -/
theorem le_zero_of_step_bound {Φ : ℝ → ℝ} {t C₃ C₄ : ℝ} (ht : 0 ≤ t) (h0 : Φ 0 = 0)
    (hstep : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t →
      Φ v - Φ u ≤ C₃ * Real.sqrt (v - u) ^ 3 + C₄ * Real.sqrt (v - u) ^ 4) :
    Φ t ≤ 0 := by
  have hb : ∀ n : ℕ, Φ t ≤ C₃ * t * Real.sqrt (t / ((n : ℝ) + 1)) +
      C₄ * t * (t / ((n : ℝ) + 1)) := by
    intro n
    set N : ℝ := (n : ℝ) + 1 with hNdef
    have hN : 0 < N := by positivity
    set τ : ℕ → ℝ := fun j => (j : ℝ) * (t / N) with hτ
    have hΔ : 0 ≤ t / N := div_nonneg ht hN.le
    have htel := Finset.sum_range_sub (fun j => Φ (τ j)) (n + 1)
    have hτN : τ (n + 1) = t := by
      simp only [hτ]; push_cast; rw [← hNdef]; field_simp
    have hτ0 : τ 0 = 0 := by simp [hτ]
    rw [hτN, hτ0, h0, sub_zero] at htel
    rw [← htel]
    have hterm : ∀ j ∈ Finset.range (n + 1), Φ (τ (j + 1)) - Φ (τ j) ≤
        C₃ * Real.sqrt (t / N) ^ 3 + C₄ * Real.sqrt (t / N) ^ 4 := by
      intro j hj
      have hjn : j < n + 1 := Finset.mem_range.mp hj
      have hj' : (j : ℝ) + 1 ≤ N := by
        rw [hNdef]; exact_mod_cast hjn
      have e : τ (j + 1) - τ j = t / N := by simp only [hτ]; push_cast; ring
      have h := hstep (τ j) (τ (j + 1)) (by simp only [hτ]; positivity)
        (by simp only [hτ]; push_cast; nlinarith)
        (by
          simp only [hτ]; push_cast
          calc ((j : ℝ) + 1) * (t / N) ≤ N * (t / N) := mul_le_mul_of_nonneg_right hj' hΔ
            _ = t := by field_simp)
      rwa [e] at h
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsq : Real.sqrt (t / N) ^ 2 = t / N := Real.sq_sqrt hΔ
    have e3 : Real.sqrt (t / N) ^ 3 = (t / N) * Real.sqrt (t / N) := by
      rw [pow_succ, hsq]
    have e4 : Real.sqrt (t / N) ^ 4 = (t / N) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    rw [e3, e4]
    have : ((n + 1 : ℕ) : ℝ) = N := by rw [hNdef]; push_cast; ring
    rw [this]
    field_simp
  have h1 : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
    exact h.congr fun n => by simp
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (t / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  have h3 := (h2.const_mul (C₃ * t)).add (h1.const_mul (C₄ * t))
  simp only [mul_zero, add_zero] at h3
  exact ge_of_tendsto' h3 hb

include hd hw hℓ in
/-- **Uniqueness for the linear equation `H = ∫ H σ dW`** (raw kit integral): `H ≡ 0`. -/
theorem eq_zero_of_eq_kitItoIntRaw {H : ℝ → Ω → ℝ} {K : ℝ}
    (hG : HolderAdapted B (fun s ω => H s ω * signatureSigma B hT ℓ s ω) T K)
    (hHI : ∀ t ∈ Icc 0 T, H t =ᵐ[P]
      kitItoIntRaw B (fun s ω => H s ω * signatureSigma B hT ℓ s ω) t) :
    ∀ t ∈ Icc 0 T, H t =ᵐ[P] 0 := by
  set G : ℝ → Ω → ℝ := fun s ω => H s ω * signatureSigma B hT ℓ s ω with hGdef
  have hGs : ∀ u ∈ Icc 0 T, ∀ᵐ ω ∂P,
      G u ω ^ 2 = kitItoIntRaw B G u ω ^ 2 * signatureSigma B hT ℓ u ω ^ 2 := by
    intro u hu
    filter_upwards [hHI u hu] with ω hω
    simp only [hGdef] at hω ⊢
    rw [hω]; ring
  obtain ⟨C₃, C₄, hstep⟩ := kitEnergy_step B hd hT hw hℓ hG hGs
  intro t ht
  have h0 : kitEnergy B hT ℓ G 0 = 0 := by simp [kitEnergy, kitItoIntRaw_zero]
  have hle := le_zero_of_step_bound ht.1 h0 fun u v hu huv hvt =>
    hstep u v hu huv (hvt.trans ht.2)
  have hQ0 : ∀ ω, 0 ≤ kitQuadVarRaw B (signatureSigma B hT ℓ) t ω := fun ω => by
    rw [kitQuadVarRaw_signatureSigma B hd hT w hw ℓ hℓ ht ω]
    exact intervalIntegral.integral_nonneg ht.1 fun r _ => sq_nonneg _
  have hIL := (kitItoIntRaw_of_holderAdapted B hd ht.1 (hG.mono ht.2)).2.1
  have hbm : AEStronglyMeasurable
      (fun ω => Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) t ω)) P :=
    (measurable_kitQuadVarRaw B _ t).neg.exp.aestronglyMeasurable
  have hi : Integrable (fun ω => kitItoIntRaw B G t ω ^ 2 *
      Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) t ω)) P :=
    integrable_mul_of_memLp_two (memLp_sq_two_of_four hIL)
      (MemLp.of_bound hbm 1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        linarith [hQ0 ω]))
  have hnn : 0 ≤ᵐ[P] fun ω => kitItoIntRaw B G t ω ^ 2 *
      Real.exp (-kitQuadVarRaw B (signatureSigma B hT ℓ) t ω) :=
    ae_of_all _ fun ω => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hz : kitEnergy B hT ℓ G t = 0 := le_antisymm hle (integral_nonneg_of_ae hnn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 hz
  filter_upwards [hae, hHI t ht] with ω h1 h2
  simp only [Pi.zero_apply, mul_eq_zero, Real.exp_ne_zero, or_false] at h1
  rw [h2]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1

end KitStep

lemma kitItoInt_of_no_driver {B : MultiBrownian Ω P d} (hd : ¬ 0 < d) (H : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) : kitItoInt B H t ω = 0 := by
  have hIto0 : kitItoIntRaw B H t = fun _ => 0 := by funext; simp [kitItoIntRaw, hd]
  have hQV0 : kitQuadVarRaw B H t = fun _ => 0 := by funext; simp [kitQuadVarRaw, hd]
  have hPair : kitPairIntegrable B H t := ⟨by simp [hIto0], by simp [hQV0]⟩
  simp [kitItoInt, hPair, hIto0, condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ)]

/-- **Pathwise uniqueness of kit strong solutions** of `dS = S σ dW` under H1–H2. -/
theorem kit_strong_solutions_eq {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) {s₀ : ℝ}
    {S₁ S₂ : ℝ → Ω → ℝ}
    (hadapt₁ : ∀ t ∈ Icc 0 T, Measurable[(prolongedBrownianSetup_stratonovich_of_brownian
      B hT).signatureFiltration.σAlg t] (S₁ t))
    (hadapt₂ : ∀ t ∈ Icc 0 T, Measurable[(prolongedBrownianSetup_stratonovich_of_brownian
      B hT).signatureFiltration.σAlg t] (S₂ t))
    (hcl₁ : KitStrongSolutionClass P T (signatureSigma B hT ℓ) S₁)
    (hcl₂ : KitStrongSolutionClass P T (signatureSigma B hT ℓ) S₂)
    (heq₁ : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₁ t ω = s₀ + kitItoInt B (fun s ω' => S₁ s ω' * signatureSigma B hT ℓ s ω') t ω)
    (heq₂ : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₂ t ω = s₀ + kitItoInt B (fun s ω' => S₂ s ω' * signatureSigma B hT ℓ s ω') t ω) :
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P, S₁ t ω = S₂ t ω := by
  by_cases hd : 0 < d
  · obtain ⟨K, hG, hD⟩ := stopped_diff_eq_raw B hd hT hadapt₁ hadapt₂ hcl₁ hcl₂ heq₁ heq₂
    have h := eq_zero_of_eq_kitItoIntRaw B hd hT hw hℓ (H := fun t ω => S₁ t ω - S₂ t ω) hG hD
    intro t ht
    filter_upwards [h t ht] with ω hω
    simp only [Pi.zero_apply] at hω
    linarith
  · intro t ht
    filter_upwards [heq₁ t ht, heq₂ t ht] with ω h1 h2
    rw [h1, h2, kitItoInt_of_no_driver hd, kitItoInt_of_no_driver hd]

end SignatureVolatility
