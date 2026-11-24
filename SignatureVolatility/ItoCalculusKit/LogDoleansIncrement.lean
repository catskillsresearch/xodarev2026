module

public import SignatureVolatility.ItoCalculusKit.QuadIncrement


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Eighth moments of increments of `log Z`

For the signature volatility under H1–H2 with a driver, `X_t = I_t - ½ ∫₀ᵗ σ²` (with `I` the raw
Itô limit) satisfies `E (X_v - X_u)⁸ ≤ K (v - u)⁴` on `[0, T]`
(`integral_logDoleans_incr_pow_eight_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

variable {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) (ℓ : ExtTensorAlgebra (d + 1))

/-- `X_t = I_t - ½ ∫₀ᵗ σ²`, the logarithm of the Doléans exponential. -/
noncomputable def logDoleans (t : ℝ) (ω : Ω) : ℝ :=
  kitItoIntRaw B (signatureSigma B hT ℓ) t ω -
    (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, signatureSigma B hT ℓ s ω ^ 2

variable {B hT ℓ}

lemma logDoleans_sub {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvT : v ≤ T) {ω : Ω}
    (hω : ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 T)) :
    logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω =
      (kitItoIntRaw B (signatureSigma B hT ℓ) v ω - kitItoIntRaw B (signatureSigma B hT ℓ) u ω) -
        (1 / 2 : ℝ) * ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2 := by
  have hc := hω.pow 2
  have hI : ∀ a, 0 ≤ a → a ≤ T →
      IntervalIntegrable (fun s => signatureSigma B hT ℓ s ω ^ 2) volume 0 a := fun a ha haT =>
    (hc.mono (by rw [uIcc_of_le ha]; exact Icc_subset_Icc le_rfl haT)).intervalIntegrable
  have h := intervalIntegral.integral_interval_sub_left (hI v (hu.trans huv) hvT)
    (hI u hu (huv.trans hvT))
  unfold logDoleans
  rw [← h]
  ring

/-- **`E (X_v - X_u)⁸ ≤ K (v - u)⁴`** for `X = log Z` under H1–H2. -/
theorem integral_logDoleans_incr_pow_eight_le (hd : 0 < d) {w : Weight} (hw : HypH2 w)
    (hℓ : HypH1 w ℓ) :
    ∃ K, 0 ≤ K ∧ ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω) ^ 8) P ∧
        ∫ ω, (logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω) ^ 8 ∂P ≤ K * (v - u) ^ 4 := by
  obtain ⟨K8, hH8⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  obtain ⟨M, hM0, hQ⟩ := integral_quadIncr_pow_eight_le (B := B) (hT := hT) (ℓ := ℓ) hw hℓ
  set C1 : ℝ := 14 ^ 4 * gauss8Const *
    (128 * ∫ ω, signatureSigma B hT ℓ 0 ω ^ 8 ∂P + 128 * K8 * T ^ 4) with hC1
  have hC10 : 0 ≤ C1 := by
    have := hH8.K_nonneg
    have := gauss8Const_nonneg
    have : 0 ≤ ∫ ω, signatureSigma B hT ℓ 0 ω ^ 8 ∂P := integral_nonneg fun ω => by positivity
    positivity
  refine ⟨128 * C1 + M * T ^ 4 / 2, by positivity, fun u v hu huv hvT => ?_⟩
  set A : Ω → ℝ := fun ω =>
    kitItoIntRaw B (signatureSigma B hT ℓ) v ω - kitItoIntRaw B (signatureSigma B hT ℓ) u ω
  set D : Ω → ℝ := fun ω => ∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2
  have hfun : (fun ω => (logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω) ^ 8) =ᵐ[P]
      fun ω => (A ω + (-(1 / 2 : ℝ) * D ω)) ^ 8 :=
    (ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ).mono fun ω hω => by
      simp only; rw [logDoleans_sub hu huv hvT hω]; ring
  obtain ⟨hAi, hAle⟩ := integral_kitItoIntRaw_sub_pow_eight_le B hd hH8 hu huv hvT
  obtain ⟨hDi, hDle⟩ := hQ u v hu huv hvT
  have hAm : Measurable A :=
    (measurable_kitItoIntRaw B _ v).sub (measurable_kitItoIntRaw B _ u)
  have hDm : AEStronglyMeasurable D P :=
    (measurable_intervalIntegral_sigmaExt huv 2).aestronglyMeasurable.congr
      ((ae_not_mem_sigmaBad hw hℓ).mono fun ω hω =>
        (intervalIntegral_sigma_eq_sigmaExt hu huv hvT 2 hω).symm)
  have hpt : ∀ ω, (A ω + (-(1 / 2 : ℝ) * D ω)) ^ 8 ≤ 128 * A ω ^ 8 + (1 / 2) * D ω ^ 8 := by
    intro ω
    have := add_pow_eight_le_conv (A ω) (-(1 / 2 : ℝ) * D ω)
    have e : (-(1 / 2 : ℝ) * D ω) ^ 8 = D ω ^ 8 / 256 := by ring
    rw [e] at this; linarith
  have hmaj : Integrable (fun ω => 128 * A ω ^ 8 + (1 / 2) * D ω ^ 8) P :=
    (hAi.const_mul 128).add (hDi.const_mul (1 / 2))
  have hint : Integrable (fun ω => (A ω + (-(1 / 2 : ℝ) * D ω)) ^ 8) P :=
    hmaj.mono' ((hAm.aestronglyMeasurable.add (hDm.const_mul _)).pow 8)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hint.congr hfun.symm, ?_⟩
  rw [integral_congr_ae hfun]
  have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
  have h84 : (v - u) ^ 8 ≤ T ^ 4 * (v - u) ^ 4 := by
    have : (v - u) ^ 4 ≤ T ^ 4 := pow_le_pow_left₀ hvu (by linarith) 4
    calc (v - u) ^ 8 = (v - u) ^ 4 * (v - u) ^ 4 := by ring
      _ ≤ T ^ 4 * (v - u) ^ 4 := mul_le_mul_of_nonneg_right this (by positivity)
  calc ∫ ω, (A ω + (-(1 / 2 : ℝ) * D ω)) ^ 8 ∂P
      ≤ ∫ ω, (128 * A ω ^ 8 + (1 / 2) * D ω ^ 8) ∂P := integral_mono hint hmaj hpt
    _ = 128 * ∫ ω, A ω ^ 8 ∂P + (1 / 2) * ∫ ω, D ω ^ 8 ∂P := by
        rw [integral_add (hAi.const_mul 128) (hDi.const_mul (1 / 2)), integral_const_mul,
          integral_const_mul]
    _ ≤ 128 * (C1 * (v - u) ^ 4) + (1 / 2) * (M * (v - u) ^ 8) := by
        gcongr
    _ ≤ 128 * (C1 * (v - u) ^ 4) + (1 / 2) * (M * (T ^ 4 * (v - u) ^ 4)) := by
        gcongr
    _ = (128 * C1 + M * T ^ 4 / 2) * (v - u) ^ 4 := by ring

end SignatureVolatility
