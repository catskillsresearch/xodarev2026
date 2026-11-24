module

public import SignatureVolatility.ItoCalculusKit.SigmaHolder8


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Eighth moments of increments of `∫ σ²`

For the signature volatility `σ` under H1–H2 and `0 ≤ u ≤ v ≤ T`,
`E (∫_u^v σ_s² ds)⁸ ≤ M (v - u)⁸` (`integral_quadIncr_pow_eight_le`). The proof uses the
pointwise power-mean bound `(∫_u^v f²)⁸ ≤ (v - u)⁷ ∫_u^v f¹⁶` (three Cauchy–Schwarz steps),
Tonelli with joint measurability of `(s, ω) ↦ σ_s(ω)` (continuity in `s`), and the uniform
moment bound `E σ_s¹⁶ ≤ M`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Cauchy–Schwarz on an interval: `(∫_u^v f)² ≤ (v - u) ∫_u^v f²`. -/
lemma sq_intervalIntegral_le {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v)) :
    (∫ s in u..v, f s) ^ 2 ≤ (v - u) * ∫ s in u..v, f s ^ 2 := by
  have hI1 : IntervalIntegrable f volume u v :=
    hf.intervalIntegrable_of_Icc huv
  have hI2 : IntervalIntegrable (fun s => f s ^ 2) volume u v :=
    (hf.pow 2).intervalIntegrable_of_Icc huv
  set I := ∫ s in u..v, f s with hI
  set J := ∫ s in u..v, f s ^ 2 with hJ
  set L := v - u with hL
  have hL0 : 0 ≤ L := sub_nonneg.mpr huv
  have hnn : 0 ≤ ∫ s in u..v, (L * f s - I) ^ 2 :=
    intervalIntegral.integral_nonneg huv fun s _ => sq_nonneg _
  have hexp : ∫ s in u..v, (L * f s - I) ^ 2 = L * (L * J - I ^ 2) := by
    have hfun : (fun s => (L * f s - I) ^ 2) =
        fun s => (L ^ 2 * f s ^ 2 - (2 * L * I) * f s) + I ^ 2 := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_add ((hI2.const_mul _).sub (hI1.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub (hI2.const_mul _)
      (hI1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    rw [← hI, ← hJ, ← hL]
    ring
  rw [hexp] at hnn
  rcases hL0.eq_or_lt with h0 | hpos
  · have huv' : u = v := by linarith
    subst huv'
    simp [hI, hL]
  · have := nonneg_of_mul_nonneg_right (by linarith [hnn] : 0 ≤ L * (L * J - I ^ 2)) hpos
    nlinarith [this]

/-- Power mean on an interval: `(∫_u^v f²)⁸ ≤ (v - u)⁷ ∫_u^v f¹⁶`. -/
lemma pow_eight_intervalIntegral_sq_le {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v)) :
    (∫ s in u..v, f s ^ 2) ^ 8 ≤ (v - u) ^ 7 * ∫ s in u..v, f s ^ 16 := by
  set L := v - u with hL
  have hL0 : 0 ≤ L := sub_nonneg.mpr huv
  set a := ∫ s in u..v, f s ^ 2
  set b := ∫ s in u..v, f s ^ 4
  set c := ∫ s in u..v, f s ^ 8
  set e := ∫ s in u..v, f s ^ 16
  have ha : 0 ≤ a := intervalIntegral.integral_nonneg huv fun s _ => by positivity
  have hb : 0 ≤ b := intervalIntegral.integral_nonneg huv fun s _ => by positivity
  have hc : 0 ≤ c := intervalIntegral.integral_nonneg huv fun s _ => by positivity
  have h1 : a ^ 2 ≤ L * b := by
    have := sq_intervalIntegral_le (f := fun s => f s ^ 2) huv (hf.pow 2)
    simpa only [← pow_mul] using this
  have h2 : b ^ 2 ≤ L * c := by
    have := sq_intervalIntegral_le (f := fun s => f s ^ 4) huv (hf.pow 4)
    simpa only [← pow_mul] using this
  have h3 : c ^ 2 ≤ L * e := by
    have := sq_intervalIntegral_le (f := fun s => f s ^ 8) huv (hf.pow 8)
    simpa only [← pow_mul] using this
  calc a ^ 8 = (a ^ 2) ^ 4 := by ring
    _ ≤ (L * b) ^ 4 := pow_le_pow_left₀ (sq_nonneg _) h1 4
    _ = L ^ 4 * (b ^ 2) ^ 2 := by ring
    _ ≤ L ^ 4 * (L * c) ^ 2 := by gcongr
    _ = L ^ 6 * c ^ 2 := by ring
    _ ≤ L ^ 6 * (L * e) := by gcongr
    _ = L ^ 7 * e := by ring

section Sigma

variable {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) (ℓ : ExtTensorAlgebra (d + 1))

/-- A measurable set (null under H1–H2) containing every `ω` whose `σ`-path is not continuous
on `[0, T]`. -/
noncomputable def sigmaBad : Set Ω :=
  toMeasurable P {ω | ¬ ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 T)}

lemma measurableSet_sigmaBad : MeasurableSet (sigmaBad B hT ℓ) :=
  measurableSet_toMeasurable _ _

open Classical in
/-- `σ` extended continuously beyond `[0, T]` by clamping time, and set to `0` on `sigmaBad`. -/
noncomputable def sigmaExt : ℝ → Ω → ℝ :=
  fun s ω => if ω ∈ sigmaBad B hT ℓ then 0 else signatureSigma B hT ℓ (projIcc 0 T hT.le s) ω

lemma sigmaExt_of_mem {s : ℝ} (hs : s ∈ Icc 0 T) {ω : Ω} (hω : ω ∉ sigmaBad B hT ℓ) :
    sigmaExt B hT ℓ s ω = signatureSigma B hT ℓ s ω := by
  simp [sigmaExt, hω, projIcc_of_mem _ hs]

variable {B hT ℓ}

lemma continuousOn_of_not_mem_sigmaBad {ω : Ω} (hω : ω ∉ sigmaBad B hT ℓ) :
    ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 T) := by
  by_contra h
  exact hω (subset_toMeasurable _ _ h)

lemma ae_not_mem_sigmaBad {w : Weight} (hw : HypH2 w) (hℓ : HypH1 w ℓ) :
    ∀ᵐ ω ∂P, ω ∉ sigmaBad B hT ℓ := by
  have h0 : P {ω | ¬ ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 T)} = 0 :=
    ae_iff.1 (ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ)
  have h1 : P (sigmaBad B hT ℓ) = 0 := by rw [sigmaBad, measure_toMeasurable]; exact h0
  exact ae_iff.2 (by simpa using h1)

lemma continuous_sigmaExt (ω : Ω) : Continuous fun s => sigmaExt B hT ℓ s ω := by
  by_cases hω : ω ∈ sigmaBad B hT ℓ
  · simp only [sigmaExt, hω, ↓reduceIte]; exact continuous_const
  · simp only [sigmaExt, hω, ↓reduceIte]
    exact (continuousOn_of_not_mem_sigmaBad hω).comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 T hT.le s).2

lemma measurable_uncurry_sigmaExt : Measurable (Function.uncurry (sigmaExt B hT ℓ)) :=
  measurable_uncurry_of_continuous_of_measurable continuous_sigmaExt fun s =>
    Measurable.ite (measurableSet_sigmaBad B hT ℓ) measurable_const
    ((measurable_signatureSigma_path B hT ℓ (projIcc 0 T hT.le s)
      ⟨projIcc 0 T hT.le s, (projIcc 0 T hT.le s).2.1, le_rfl⟩).mono
      ((pathFiltration B).le_ambient _) le_rfl)

lemma intervalIntegral_sigma_eq_sigmaExt {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T)
    (k : ℕ) {ω : Ω} (hω : ω ∉ sigmaBad B hT ℓ) :
    ∫ s in u..v, signatureSigma B hT ℓ s ω ^ k = ∫ s in u..v, sigmaExt B hT ℓ s ω ^ k := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le huv] at hs
  rw [sigmaExt_of_mem B hT ℓ ⟨hu.trans hs.1, hs.2.trans hvT⟩ hω]

lemma measurable_intervalIntegral_sigmaExt {u v : ℝ} (huv : u ≤ v) (k : ℕ) :
    Measurable fun ω => ∫ s in u..v, sigmaExt B hT ℓ s ω ^ k := by
  have hm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => sigmaExt B hT ℓ s ω ^ k) :=
    (measurable_uncurry_sigmaExt.comp measurable_swap).pow_const k
  have h := hm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc u v))
  simp only [intervalIntegral.integral_of_le huv]
  exact h.measurable

/-- **Uniform sixteenth moments of `σ = ⟨ℓ, Ŵ⟩`** on `[0, T]` under H1–H2. -/
theorem signatureSigma_pow16_moment {w : Weight} (hw : HypH2 w) (hℓ : HypH1 w ℓ) :
    ∃ Cσ, 0 ≤ Cσ ∧ ∀ s ∈ Icc 0 T,
      Integrable (fun ω => signatureSigma B hT ℓ s ω ^ 16) P ∧
      ∫ ω, signatureSigma B hT ℓ s ω ^ 16 ∂P ≤ Cσ := by
  obtain ⟨C, r, hC, hr, hℓn⟩ := exists_levelNorm_le_geometric hw hℓ
  obtain ⟨M, hM0, hM⟩ := dualPairing_paperSig2_moment (P := P) B hC hr hℓn (q := 8)
    (by norm_num) (t := T)
  refine ⟨M, hM0, fun s hs => ?_⟩
  obtain ⟨-, hL, hI⟩ := hM s hs.1 hs.2
  exact ⟨integrable_pow_of_memLp_evenDeg ⟨8, rfl⟩ hL, hI⟩

/-- **Eighth moments of increments of `∫ σ²`** under H1–H2. -/
theorem integral_quadIncr_pow_eight_le {w : Weight} (hw : HypH2 w) (hℓ : HypH1 w ℓ) :
    ∃ M, 0 ≤ M ∧ ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8) P ∧
        ∫ ω, (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8 ∂P ≤ M * (v - u) ^ 8 := by
  obtain ⟨M, hM0, hmom16⟩ := signatureSigma_pow16_moment (B := B) (hT := hT) hw hℓ
  refine ⟨M, hM0, fun u v hu huv hvT => ?_⟩
  set G : Ω → ℝ := fun ω => ∫ s in u..v, sigmaExt B hT ℓ s ω ^ 16 with hG
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω =>
    intervalIntegral.integral_nonneg huv fun s _ => by positivity
  have hGm : Measurable G := measurable_intervalIntegral_sigmaExt huv 16
  have hcont : ∀ ω, Continuous fun s => sigmaExt B hT ℓ s ω ^ 16 := fun ω =>
    (continuous_sigmaExt ω).pow 16
  have hstep1 : ∀ ω, ENNReal.ofReal (G ω) =
      ∫⁻ s in Ioc u v, ENNReal.ofReal (sigmaExt B hT ℓ s ω ^ 16) := by
    intro ω
    simp only [hG]
    rw [intervalIntegral.integral_of_le huv]
    exact ofReal_integral_eq_lintegral_ofReal
      (((hcont ω).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun s => by positivity)
  have hm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (sigmaExt B hT ℓ s ω ^ 16)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_uncurry_sigmaExt.comp measurable_swap).pow_const 16)
  have hlint : ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ ENNReal.ofReal (M * (v - u)) := by
    calc ∫⁻ ω, ENNReal.ofReal (G ω) ∂P
        = ∫⁻ ω, (∫⁻ s in Ioc u v, ENNReal.ofReal (sigmaExt B hT ℓ s ω ^ 16)) ∂P :=
          lintegral_congr hstep1
      _ = ∫⁻ s in Ioc u v, ∫⁻ ω, ENNReal.ofReal (sigmaExt B hT ℓ s ω ^ 16) ∂P :=
          lintegral_lintegral_swap hm.aemeasurable
      _ ≤ ∫⁻ s in Ioc u v, ENNReal.ofReal M := by
          refine setLIntegral_mono measurable_const fun s hs => ?_
          have hs' : s ∈ Icc 0 T := ⟨hu.trans hs.1.le, hs.2.trans hvT⟩
          have hmom := hmom16 s hs'
          have hfun : (fun ω => ENNReal.ofReal (sigmaExt B hT ℓ s ω ^ 16)) =ᵐ[P]
              fun ω => ENNReal.ofReal (signatureSigma B hT ℓ s ω ^ 16) :=
            (ae_not_mem_sigmaBad hw hℓ).mono fun ω hω => by
              simp only; rw [sigmaExt_of_mem B hT ℓ hs' hω]
          rw [lintegral_congr_ae hfun, ← ofReal_integral_eq_lintegral_ofReal hmom.1
            (ae_of_all _ fun ω => by positivity)]
          exact ENNReal.ofReal_le_ofReal hmom.2
      _ = ENNReal.ofReal (M * (v - u)) := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hM0]
  have hGi : Integrable G P := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) (hlint.trans_lt ENNReal.ofReal_lt_top)
    rw [Real.enorm_eq_ofReal (hG0 ω)]
  have hGle : ∫ ω, G ω ∂P ≤ M * (v - u) := by
    have hMv : 0 ≤ M * (v - u) := mul_nonneg hM0 (sub_nonneg.mpr huv)
    rw [← ENNReal.ofReal_le_ofReal_iff hMv, ofReal_integral_eq_lintegral_ofReal hGi
      (ae_of_all _ hG0)]
    exact hlint
  have hQ : ∀ᵐ ω ∂P, ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2 =
      ∫ s in u..v, sigmaExt B hT ℓ s ω ^ 2 := (ae_not_mem_sigmaBad hw hℓ).mono fun ω hω =>
    intervalIntegral_sigma_eq_sigmaExt hu huv hvT 2 hω
  have hpt : ∀ᵐ ω ∂P, (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8 ≤ (v - u) ^ 7 * G ω :=
    hQ.mono fun ω h => by
      rw [h]
      exact pow_eight_intervalIntegral_sq_le huv (continuous_sigmaExt ω).continuousOn
  have hQm : AEStronglyMeasurable
      (fun ω => (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8) P :=
    ((measurable_intervalIntegral_sigmaExt huv 2).pow_const 8).aestronglyMeasurable.congr
      (hQ.mono fun ω h => by simp only; rw [h])
  have hQi : Integrable (fun ω => (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8) P :=
    (hGi.const_mul ((v - u) ^ 7)).mono' hQm (hpt.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact h)
  refine ⟨hQi, ?_⟩
  calc ∫ ω, (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) ^ 8 ∂P
      ≤ ∫ ω, (v - u) ^ 7 * G ω ∂P := integral_mono_ae hQi (hGi.const_mul _) hpt
    _ = (v - u) ^ 7 * ∫ ω, G ω ∂P := integral_const_mul _ _
    _ ≤ (v - u) ^ 7 * (M * (v - u)) :=
        mul_le_mul_of_nonneg_left hGle (pow_nonneg (sub_nonneg.mpr huv) 7)
    _ = M * (v - u) ^ 8 := by ring

end Sigma

end SignatureVolatility
