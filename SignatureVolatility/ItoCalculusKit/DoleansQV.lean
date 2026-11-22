module

public import SignatureVolatility.ItoCalculusKit.KolmogorovIto

@[expose] public section

open MeasureTheory Filter Topology Finset
open scoped NNReal

namespace SignatureVolatility

/-!
# The quadratic-variation half of the Doléans integrability gate

For `H = s₀ Z σ` (signature volatility, H1–H3, `t ∈ [0, T]`), the raw quadratic variation
`limUnder ∑ H(τⱼ)² δ` is Bochner-integrable (`integrable_kitQuadVarRaw_doleans`): along a
continuous (Kolmogorov) version of `∫ σ dW`, the Riemann sums converge almost surely, and Fatou
with `𝔼 H_s² ≤ C` uniformly on `[0, T]` bounds the limit.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- Fatou, almost-everywhere form: an a.e. limit of nonnegative integrable functions with
bounded integrals is integrable. -/
lemma integrable_of_ae_tendsto_of_integral_le {R : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hRm : ∀ n, Measurable (R n)) (hR0 : ∀ n ω, 0 ≤ R n ω) (hRi : ∀ n, Integrable (R n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (L ω))) {C : ℝ}
    (hC : ∀ n, ∫ ω, R n ω ∂P ≤ C) : Integrable L P := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hRm n).aestronglyMeasurable) hlim,
    ?_⟩
  have h1 : ∫⁻ ω, ‖L ω‖ₑ ∂P = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (R n ω)) atTop ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with ω hω
    have hL0 : 0 ≤ L ω := ge_of_tendsto' hω fun n => hR0 n ω
    rw [Real.enorm_eq_ofReal hL0]
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq.symm
  rw [HasFiniteIntegral, h1]
  refine lt_of_le_of_lt (lintegral_liminf_le fun n => (hRm n).ennreal_ofReal) ?_
  refine lt_of_le_of_lt (liminf_le_of_le (by isBoundedDefault) fun b hb => ?_)
    (ENNReal.ofReal_lt_top (r := C))
  obtain ⟨n, hn⟩ := hb.exists
  refine hn.trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hRi n) (ae_of_all _ (hR0 n))]
  exact ENNReal.ofReal_le_ofReal (hC n)

lemma sq_mul_sq_le_moments (z s : ℝ) : z ^ 2 * s ^ 2 ≤ ((1 + z ^ 8) + (2 + s ^ 16)) / 2 := by
  have h1 : z ^ 2 * s ^ 2 ≤ (z ^ 4 + s ^ 4) / 2 := by nlinarith [sq_nonneg (z ^ 2 - s ^ 2)]
  have h2 : z ^ 4 ≤ 1 + z ^ 8 := by nlinarith [sq_nonneg (z ^ 4 - 1), pow_two_nonneg (z ^ 4)]
  have h3 : s ^ 4 ≤ 1 + s ^ 8 := by nlinarith [sq_nonneg (s ^ 4 - 1), pow_two_nonneg (s ^ 4)]
  have h4 : s ^ 8 ≤ 1 + s ^ 16 := by nlinarith [sq_nonneg (s ^ 8 - 1), pow_two_nonneg (s ^ 8)]
  linarith

section QV

variable {T : ℝ} (B : MultiBrownian Ω P d)

/-- **Second half of the integrability gate**: the raw quadratic variation of `s₀ Z σ` is
integrable. -/
theorem integrable_kitQuadVarRaw_doleans (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (s₀ : ℝ) :
    Integrable (kitQuadVarRaw B (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
        signatureSigma B hT ℓ s ω') t) P := by
  set σ := signatureSigma B hT ℓ with hσ
  set Z := kitDoleansExp B σ with hZ
  set H : ℝ → Ω → ℝ := fun s ω' => (s₀ * Z s ω') * σ s ω' with hHdef
  set δ : ℕ → ℝ := fun n => t / ((n : ℝ) + 1) with hδ
  set τ : ℕ → ℕ → ℝ := fun n j => (j : ℝ) * (t / ((n : ℝ) + 1)) with hτ
  have hτ0 : ∀ n j, 0 ≤ τ n j := fun n j => by simp only [hτ]; have := ht.1; positivity
  have hτt : ∀ n j, j < n + 1 → τ n j ≤ t := fun n j hj => by
    have := gridPt_le ht.1 hj.le (n := n)
    simp only [gridPt] at this; push_cast at this; exact this
  have hτT : ∀ n j, j < n + 1 → τ n j ∈ Set.Icc 0 T := fun n j hj =>
    ⟨hτ0 n j, (hτt n j hj).trans ht.2⟩
  set R : ℕ → Ω → ℝ := fun n ω => ∑ j ∈ range (n + 1), H (τ n j) ω ^ 2 * δ n with hRdef
  -- the raw quadratic variation is the `limUnder` of `R`
  have hraw : ∀ ω, kitQuadVarRaw B H t ω = limUnder atTop fun n => R n ω := by
    intro ω
    simp only [kitQuadVarRaw, hd, ↓reduceIte, lebIntegral_process, ht.1, ↓reduceDIte]
    congr 1
    funext n
    simp only [lebRiemann_process, zero_add, sub_zero, Nat.cast_add, Nat.cast_one, hRdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : Measurable[(pathFiltration B).σAlg (τ n j)] (H (τ n j)) :=
      ((kitDoleansExp_adapted_path B σ (τ n j) ⟨τ n j, hτ0 n j, le_rfl⟩).const_mul s₀).mul
        (measurable_signatureSigma_path B hT ℓ (τ n j) ⟨τ n j, hτ0 n j, le_rfl⟩)
    rw [forceMeasurableProcess_eq_of_adapted B hm]
    ring
  -- moments
  obtain ⟨Cz, hCz0, hCz⟩ := exists_integral_kitDoleansExp_pow_eight_le B hd hT hw hℓ h3
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_integral_signatureSigma_pow_sixteen_le B hT hw hℓ
  obtain ⟨K, hH8⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  set C1 : ℝ := s₀ ^ 2 * ((1 + Cz) + (2 + Cσ)) / 2 with hC1
  have hσm : ∀ s ∈ Set.Icc 0 T, Measurable (σ s) := fun s hs =>
    (hH8.meas s hs.1 hs.2).mono ((pathFiltration B).le_ambient _) le_rfl
  have hHm : ∀ s ∈ Set.Icc 0 T, Measurable (H s) := fun s hs =>
    ((measurable_kitDoleansExp B σ s).const_mul s₀).mul (hσm s hs)
  have hpt : ∀ s ∈ Set.Icc 0 T, Integrable (fun ω => H s ω ^ 2) P ∧
      ∫ ω, H s ω ^ 2 ∂P ≤ C1 := by
    intro s hs
    have hZ8 := integrable_pow_of_memLp_eight (hCz s hs).1 (k := 8) le_rfl
    have hD : Integrable (fun ω => s₀ ^ 2 * ((1 + Z s ω ^ 8) + (2 + σ s ω ^ 16)) / 2) P :=
      ((((integrable_const 1).add hZ8).add ((integrable_const 2).add (hCσ s hs).1)).const_mul
        (s₀ ^ 2)).div_const 2
    have hle : ∀ ω, H s ω ^ 2 ≤ s₀ ^ 2 * ((1 + Z s ω ^ 8) + (2 + σ s ω ^ 16)) / 2 := by
      intro ω
      have := sq_mul_sq_le_moments (Z s ω) (σ s ω)
      have hs0 : 0 ≤ s₀ ^ 2 := sq_nonneg _
      calc H s ω ^ 2 = s₀ ^ 2 * (Z s ω ^ 2 * σ s ω ^ 2) := by simp only [hHdef]; ring
        _ ≤ s₀ ^ 2 * (((1 + Z s ω ^ 8) + (2 + σ s ω ^ 16)) / 2) :=
            mul_le_mul_of_nonneg_left this hs0
        _ = _ := by ring
    have hI : Integrable (fun ω => H s ω ^ 2) P :=
      hD.mono' ((hHm s hs).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle ω)
    refine ⟨hI, (integral_mono hI hD hle).trans ?_⟩
    have hA : Integrable (fun ω => 1 + Z s ω ^ 8) P := (integrable_const 1).add hZ8
    have hB : Integrable (fun ω => 2 + σ s ω ^ 16) P := (integrable_const 2).add (hCσ s hs).1
    have hZ8' : Integrable (fun ω => Z s ω ^ 8) P := hZ8
    have hσ16 : Integrable (fun ω => σ s ω ^ 16) P := (hCσ s hs).1
    rw [integral_div, integral_const_mul, integral_add hA hB,
      integral_add (integrable_const 1) hZ8', integral_add (integrable_const 2) hσ16]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have h1 := (hCz s hs).2
    have h2 := (hCσ s hs).2
    rw [hC1]
    have hs0 : 0 ≤ s₀ ^ 2 := sq_nonneg _
    gcongr
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => by simp only [hδ]; have := ht.1; positivity
  have hRm : ∀ n, Measurable (R n) := fun n => Finset.measurable_sum _ fun j hj =>
    ((hHm _ (hτT n j (mem_range.mp hj))).pow_const 2).mul_const _
  have hR0 : ∀ n ω, 0 ≤ R n ω := fun n ω =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hδ0 n)
  have hRi : ∀ n, Integrable (R n) P := fun n =>
    integrable_finsetSum _ fun j hj => ((hpt _ (hτT n j (mem_range.mp hj))).1).mul_const _
  have hRC : ∀ n, ∫ ω, R n ω ∂P ≤ C1 * t := by
    intro n
    simp only [hRdef]
    rw [integral_finsetSum _ fun j hj => ((hpt _ (hτT n j (mem_range.mp hj))).1).mul_const _]
    calc ∑ j ∈ range (n + 1), ∫ ω, H (τ n j) ω ^ 2 * δ n ∂P
        = ∑ j ∈ range (n + 1), (∫ ω, H (τ n j) ω ^ 2 ∂P) * δ n :=
          sum_congr rfl fun j _ => integral_mul_const _ _
      _ ≤ ∑ _j ∈ range (n + 1), C1 * δ n :=
          sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
            (hpt _ (hτT n j (mem_range.mp hj))).2 (hδ0 n)
      _ = C1 * t := by
          rw [sum_const, card_range, nsmul_eq_mul]
          simp only [hδ]
          have : (n : ℝ) + 1 ≠ 0 := by positivity
          push_cast
          field_simp
  obtain ⟨Y, hYc, hYeq⟩ := exists_continuous_version_kitItoIntRaw B hd (hH8.mono ht.2) ht.1
  have hgood : ∀ᵐ ω ∂P, ∀ n j, j < n + 1 →
      Y (Real.toNNReal (τ n j)) ω = kitItoIntRaw B σ (τ n j) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro j
    by_cases hj : j < n + 1
    · have hc : ((Real.toNNReal (τ n j) : ℝ≥0) : ℝ) = τ n j := Real.coe_toNNReal _ (hτ0 n j)
      filter_upwards [hYeq (Real.toNNReal (τ n j)) (by rw [hc]; exact hτt n j hj)] with ω hω _
      rw [hω, hc]
    · exact ae_of_all _ fun ω h => absurd h hj
  refine integrable_of_ae_tendsto_of_integral_le hRm hR0 hRi ?_ hRC
  filter_upwards [hgood] with ω hω
  have hσc : ContinuousOn (fun s => σ s ω) (Set.Icc 0 t) :=
    (continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).mono (Set.Icc_subset_Icc_right ht.2)
  have hprim : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, σ u ω ^ 2) (Set.Icc 0 t) := by
    have hc2 : ContinuousOn (fun u => σ u ω ^ 2) (Set.uIcc 0 t) := by
      rw [Set.uIcc_of_le ht.1]; exact hσc.pow 2
    have := intervalIntegral.continuousOn_primitive_interval' hc2.intervalIntegrable
      Set.left_mem_uIcc (μ := MeasureTheory.volume)
    rwa [Set.uIcc_of_le ht.1] at this
  have hYs : Continuous fun s : ℝ => Y (Real.toNNReal s) ω := (hYc ω).comp continuous_real_toNNReal
  have hg : ContinuousOn (fun s => (s₀ * Real.exp (Y (Real.toNNReal s) ω -
      (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..s, σ u ω ^ 2) * σ s ω) ^ 2) (Set.Icc 0 t) :=
    ((continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (hYs.continuousOn.sub (continuousOn_const.mul hprim)))).mul hσc).pow 2
  have hlim := tendsto_lebRiemann_of_continuousOn ht.1 hg
  have heq : ∀ n, R n ω = ∑ j ∈ range (n + 1),
      (s₀ * Real.exp (Y (Real.toNNReal (τ n j)) ω -
        (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(τ n j), σ u ω ^ 2) * σ (τ n j) ω) ^ 2 *
        (t / ((n : ℝ) + 1)) := by
    intro n
    refine sum_congr rfl fun j hj => ?_
    have hjl := mem_range.mp hj
    have e : Z (τ n j) ω = Real.exp (Y (Real.toNNReal (τ n j)) ω -
        (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(τ n j), σ u ω ^ 2) := by
      rw [hω n j hjl]
      exact kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 (hτT n j hjl) ω
    show (s₀ * Z (τ n j) ω * σ (τ n j) ω) ^ 2 * (t / ((n : ℝ) + 1)) = _
    rw [e]
  have hR' : Tendsto (fun n => R n ω) atTop _ := hlim.congr fun n => (heq n).symm
  rw [hraw ω, hR'.limUnder_eq]
  exact hR'

end QV

end SignatureVolatility
