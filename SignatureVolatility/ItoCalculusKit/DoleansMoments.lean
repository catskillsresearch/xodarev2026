module

public import SignatureVolatility.HypH3
public import SignatureVolatility.ItoCalculusKit.ExpSupermartingale
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto
public import SignatureVolatility.ItoCalculusKit.SigmaHolder


@[expose] public section

open MeasureTheory Filter Topology Set

namespace SignatureVolatility

/-!
# Moments of the Doléans exponential of the signature volatility

* `kitItoIntRaw_signatureSigma`: a.s. full-sequence convergence of the Itô–Riemann sums of `σ`
  and `L⁴` of the raw limit `I_t` (H1–H2).
* `lintegral_exp_signatureSigma_le_one`: `E exp (q I_t - q²/2 ∫₀ᵗ σ²) ≤ 1` for every `q`.
* `lintegral_exp_mul_signatureSigma_lt_top`: under H3, `E exp (p (I_t - ½ ∫₀ᵗ σ²)) < ∞` for
  `p ≥ 1`, i.e. all moments of the Doléans exponential are finite.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Raw Itô limit of the signature volatility** (H1–H2): the Itô–Riemann sums of `σ` converge
almost surely along the full sequence of uniform grids, and the raw limit is in `L⁴`, hence
integrable (`holderAdapted_signatureSigma` + `kitItoIntRaw_of_holderAdapted`). -/
theorem kitItoIntRaw_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B (kitDriver hd) (signatureSigma B hT ℓ) t
      (n + 1) ω) atTop (𝓝 (kitItoIntRaw B (signatureSigma B hT ℓ) t ω))) ∧
      MemLp (kitItoIntRaw B (signatureSigma B hT ℓ) t) 4 P ∧
      Integrable (kitItoIntRaw B (signatureSigma B hT ℓ) t) P := by
  obtain ⟨K, hK⟩ := holderAdapted_signatureSigma B hT hw hℓ t
  exact kitItoIntRaw_of_holderAdapted B hd ht hK

/-- Pathwise convergence of the uniform-grid Lebesgue sums of `σ²` to `∫₀ᵗ σ²`. -/
lemma tendsto_sum_sq_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (ω : Ω) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      signatureSigma B hT ℓ ((i : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω ^ 2 *
        (t / ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2)) := by
  have hcont : ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 t) :=
    (continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).mono (Icc_subset_Icc_right ht.2)
  have h := tendsto_lebRiemann_of_continuousOn ht.1 (hcont.pow 2)
  simpa only [Nat.cast_add, Nat.cast_one, Pi.pow_apply] using h

/-- **Exponential supermartingale bound for the signature volatility** (H1–H2). -/
theorem lintegral_exp_signatureSigma_le_one {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (q : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (q * kitItoIntRaw B (signatureSigma B hT ℓ) t ω -
      q ^ 2 / 2 * ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2)) ∂P ≤ 1 :=
  lintegral_exp_ito_le_one B (kitDriver hd) ht.1
    (fun u h0 _ => measurable_signatureSigma_path B hT ℓ u ⟨u, h0, le_rfl⟩) q
    (kitItoIntRaw_signatureSigma B hd hT hw hℓ ht.1).1
    (ae_of_all _ fun ω => tendsto_sum_sq_signatureSigma B hT hw hℓ ht ω)

/-- **All moments of the Doléans exponential** (H1–H3): for `p ≥ 1`,
`E exp (p (I_t - ½ ∫₀ᵗ σ²)) ≤ 1 + E exp ((2p² - p) ∫₀ᵀ σ²) < ∞`. -/
theorem lintegral_exp_mul_signatureSigma_le {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Icc 0 T) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (p * (kitItoIntRaw B (signatureSigma B hT ℓ) t ω -
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2))) ∂P ≤
      1 + ENNReal.ofReal (∫ ω, Real.exp ((2 * p ^ 2 - p) *
        ∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2) ∂P) := by
  set I := kitItoIntRaw B (signatureSigma B hT ℓ) t
  set Qt : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2 with hQt
  set QT : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2 with hQT
  set lam : ℝ := 2 * p ^ 2 - p with hlam
  have hlam0 : 0 < lam := by nlinarith
  have hH3 := h3 lam hlam0
  have hQle : ∀ ω, Qt ω ≤ QT ω := fun ω =>
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ fun s => sq_nonneg _)
      (((continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).pow 2).intervalIntegrable_of_Icc hT.le)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (p * (I ω - (1 / 2 : ℝ) * Qt ω))) ≤
      ENNReal.ofReal (Real.exp ((2 * p) * I ω - (2 * p) ^ 2 / 2 * Qt ω)) +
        ENNReal.ofReal (Real.exp (lam * QT ω)) := by
    intro ω
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    set x := Real.exp (p * I ω - p ^ 2 * Qt ω)
    set y := Real.exp ((p ^ 2 - p / 2) * Qt ω)
    have hxy : Real.exp (p * (I ω - (1 / 2 : ℝ) * Qt ω)) = x * y := by
      rw [← Real.exp_add]; congr 1; ring
    have hx2 : Real.exp ((2 * p) * I ω - (2 * p) ^ 2 / 2 * Qt ω) = x ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hy2 : y ^ 2 ≤ Real.exp (lam * QT ω) := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have : (↑(2 : ℕ) : ℝ) * ((p ^ 2 - p / 2) * Qt ω) = lam * Qt ω := by push_cast; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (hQle ω) hlam0.le
    rw [hxy, hx2]
    have hx0 : 0 ≤ x := (Real.exp_pos _).le
    have hy0 : 0 ≤ y := (Real.exp_pos _).le
    nlinarith [sq_nonneg (x - y)]
  have hmeasR : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (lam * QT ω))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hH3.aemeasurable
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (p * (I ω - (1 / 2 : ℝ) * Qt ω))) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp ((2 * p) * I ω - (2 * p) ^ 2 / 2 * Qt ω)) +
          ENNReal.ofReal (Real.exp (lam * QT ω))) ∂P := lintegral_mono hpt
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * p) * I ω - (2 * p) ^ 2 / 2 * Qt ω)) ∂P +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * QT ω)) ∂P := lintegral_add_right' _ hmeasR
    _ ≤ 1 + ENNReal.ofReal (∫ ω, Real.exp (lam * QT ω) ∂P) := by
        gcongr
        · exact lintegral_exp_signatureSigma_le_one B hd hT hw hℓ ht (2 * p)
        · rw [ofReal_integral_eq_lintegral_ofReal hH3 (ae_of_all _ fun ω => (Real.exp_pos _).le)]

end SignatureVolatility
