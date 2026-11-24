module

public import SignatureVolatility.ItoCalculusKit.DoleansErrorPathwise
public import SignatureVolatility.ItoCalculusKit.DoleansSigma
public import SignatureVolatility.ItoCalculusKit.QuadIncrement

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Almost-sure inputs for the Doléans identification

For the signature volatility `σ = ⟨ℓ, Ŵ⟩` under H1–H3 and `t ∈ [0, T]`, on the uniform grids
`τᵢ = i t / (n + 1)`:

* uniform moment bounds `𝔼 Z_s⁸ ≤ C`, `𝔼 σ_s¹⁶ ≤ C`, `𝔼 (Z_s σ_s²)⁴ ≤ C` on `[0, T]`;
* `∑ Z(τᵢ) aᵢ → 0` a.s., where `aᵢ` is the frozen increment of `∫ σ dW`;
* `∑ aᵢ² → 0` a.s.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Uniform grid point `i t / (n + 1)`. -/
noncomputable def gridPt (t : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (t / ((n + 1 : ℕ) : ℝ))

lemma gridPt_nonneg {t : ℝ} (ht : 0 ≤ t) (n i : ℕ) : 0 ≤ gridPt t n i :=
  mul_nonneg (Nat.cast_nonneg _) (div_nonneg ht (Nat.cast_nonneg _))

lemma gridPt_mono {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : Monotone (gridPt t n) := fun i j hij =>
  mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (div_nonneg ht (Nat.cast_nonneg _))

lemma gridPt_le {t : ℝ} (ht : 0 ≤ t) {n i : ℕ} (hi : i ≤ n + 1) : gridPt t n i ≤ t :=
  (unifGrid_mem ht (Nat.succ_pos n) hi).2

lemma gridPt_last (t : ℝ) (n : ℕ) : gridPt t n (n + 1) = t := by
  unfold gridPt
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma gridPt_succ_sub (t : ℝ) (n i : ℕ) :
    gridPt t n (i + 1) - gridPt t n i = t / ((n + 1 : ℕ) : ℝ) := by
  unfold gridPt; push_cast; ring

lemma sum_gridPt_sub_sq (t : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (gridPt t n (i + 1) - gridPt t n i) ^ 2 =
      t ^ 2 * (1 / ((n + 1 : ℕ) : ℝ)) := by
  simp_rw [gridPt_succ_sub, sum_const, card_range, nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma summable_one_div_succ_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hp)

/-- Product of two `L⁸` functions is in `L⁴`. -/
lemma memLp_mul_four_of_eight {f g : Ω → ℝ} (hf : MemLp f 8 P) (hg : MemLp g 8 P) :
    MemLp (fun ω => f ω * g ω) 4 P := by
  refine memLp_four_of_integrable_pow_four
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  exact (integrable_mul_of_memLp_two (memLp_pow_four_two hf) (memLp_pow_four_two hg)).congr
    (ae_of_all _ fun ω => by simp only; ring)

section Inputs

variable {T : ℝ} (B : MultiBrownian Ω P d)

/-- **Uniform eighth moment of the Doléans exponential** on `[0, T]` (H1–H3). -/
theorem exists_integral_kitDoleansExp_pow_eight_le (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) :
    ∃ Cz, 0 ≤ Cz ∧ ∀ s ∈ Set.Icc 0 T, MemLp (kitDoleansExp B (signatureSigma B hT ℓ) s) 8 P ∧
      ∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8 ∂P ≤ Cz := by
  set R : ℝ := ∫ ω, Real.exp ((2 * (8 : ℝ) ^ 2 - 8) *
    ∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2) ∂P with hR
  have hR0 : 0 ≤ R := integral_nonneg fun ω => (Real.exp_pos _).le
  refine ⟨1 + R, by linarith, fun s hs => ?_⟩
  have hL : MemLp (kitDoleansExp B (signatureSigma B hT ℓ) s) 8 P := by
    have := memLp_kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 hs 8 (by norm_num)
    exact_mod_cast this
  refine ⟨hL, ?_⟩
  have hint := integrable_pow_of_memLp_eight hL (k := 8) le_rfl
  have hlin := lintegral_exp_mul_signatureSigma_le B hd hT hw hℓ h3 hs (p := 8) (by norm_num)
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8) =
      ENNReal.ofReal (Real.exp (8 * (kitItoIntRaw B (signatureSigma B hT ℓ) s ω -
        (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..s, (signatureSigma B hT ℓ u ω) ^ 2))) := by
    filter_upwards [ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ] with ω hω
    rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hs hω, ← Real.exp_nat_mul]
    norm_num
  have h1 : ENNReal.ofReal (∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8 ∂P) =
      ∫⁻ ω, ENNReal.ofReal (kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)
  have h2 : ENNReal.ofReal (∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8 ∂P) ≤
      ENNReal.ofReal (1 + R) := by
    rw [h1, ENNReal.ofReal_add zero_le_one hR0, ENNReal.ofReal_one]
    rw [lintegral_congr_ae hpt]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2

/-- **Uniform sixteenth moment of the signature volatility** on `[0, T]`. -/
theorem exists_integral_signatureSigma_pow_sixteen_le (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) :
    ∃ Cσ, 0 ≤ Cσ ∧ ∀ s ∈ Set.Icc 0 T,
      Integrable (fun ω => signatureSigma B hT ℓ s ω ^ 16) P ∧
      ∫ ω, signatureSigma B hT ℓ s ω ^ 16 ∂P ≤ Cσ :=
  signatureSigma_pow16_moment (B := B) (hT := hT) hw hℓ

/-- **Uniform fourth moment of `Z σ²`** on `[0, T]`. -/
theorem exists_integral_kitDoleansExp_mul_sq_pow_four_le (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) :
    ∃ Ch, 0 ≤ Ch ∧ ∀ s ∈ Set.Icc 0 T,
      MemLp (fun ω => kitDoleansExp B (signatureSigma B hT ℓ) s ω *
        signatureSigma B hT ℓ s ω ^ 2) 4 P ∧
      ∫ ω, (kitDoleansExp B (signatureSigma B hT ℓ) s ω *
        signatureSigma B hT ℓ s ω ^ 2) ^ 4 ∂P ≤ Ch := by
  obtain ⟨Cz, hCz0, hCz⟩ := exists_integral_kitDoleansExp_pow_eight_le B hd hT hw hℓ h3
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_integral_signatureSigma_pow_sixteen_le B hT hw hℓ
  obtain ⟨K, hH⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  refine ⟨Real.sqrt Cz * Real.sqrt Cσ, by positivity, fun s hs => ?_⟩
  obtain ⟨hZ8, hZb⟩ := hCz s hs
  obtain ⟨hσi, hσb⟩ := hCσ s hs
  have hσm : Measurable (signatureSigma B hT ℓ s) :=
    (hH.meas s hs.1 hs.2).mono ((pathFiltration B).le_ambient _) le_rfl
  have hZ4 := memLp_pow_four_two hZ8
  have hσ8 : MemLp (fun ω => signatureSigma B hT ℓ s ω ^ 8) 2 P :=
    (memLp_two_iff_integrable_sq (hσm.pow_const 8).aestronglyMeasurable).mpr
      (hσi.congr (ae_of_all _ fun ω => by simp only; ring))
  have hprod := integrable_mul_of_memLp_two hZ4 hσ8
  have heq : ∀ ω, (kitDoleansExp B (signatureSigma B hT ℓ) s ω *
      signatureSigma B hT ℓ s ω ^ 2) ^ 4 =
      kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 4 * signatureSigma B hT ℓ s ω ^ 8 :=
    fun ω => by ring
  refine ⟨memLp_four_of_integrable_pow_four
    ((measurable_kitDoleansExp B _ s).mul (hσm.pow_const 2)).aestronglyMeasurable
    (hprod.congr (ae_of_all _ fun ω => (heq ω).symm)), ?_⟩
  simp_rw [heq]
  have hcs := abs_integral_mul_le_sqrt hZ4 hσ8
  have e1 : ∫ ω, (kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 4) ^ 2 ∂P =
      ∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 8 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only; ring)
  have e2 : ∫ ω, (signatureSigma B hT ℓ s ω ^ 8) ^ 2 ∂P =
      ∫ ω, signatureSigma B hT ℓ s ω ^ 16 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only; ring)
  rw [e1, e2] at hcs
  calc _ ≤ |∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ 4 *
        signatureSigma B hT ℓ s ω ^ 8 ∂P| := le_abs_self _
    _ ≤ _ := hcs
    _ ≤ _ := by gcongr

/-- Frozen increments of `∫ σ dW` on the grid are in `L⁸` with the `(v - u)⁸` bound. -/
lemma frozenIncr_grid_bound (hd : 0 < d) {H : ℝ → Ω → ℝ} {t K : ℝ} (hH : HolderAdapted8 B H t K)
    (ht : 0 ≤ t) (n i : ℕ) (hi : i < n + 1) :
    Measurable (frozenIncr B hd H (gridPt t n i) (gridPt t n (i + 1))) ∧
    MemLp (frozenIncr B hd H (gridPt t n i) (gridPt t n (i + 1))) 8 P ∧
    ∫ ω, frozenIncr B hd H (gridPt t n i) (gridPt t n (i + 1)) ω ^ 8 ∂P ≤
      128 * 14 ^ 4 * gauss8Const * K * (t / ((n + 1 : ℕ) : ℝ)) ^ 8 := by
  have h0 := gridPt_nonneg ht n i
  have h1 := gridPt_mono ht n (Nat.le_succ i)
  have h2 := gridPt_le ht (Nat.succ_le_of_lt hi)
  have hb := integral_kitItoIntRaw_sub_frozen_pow_eight_le B hd hH h0 h1 h2
  have hm : Measurable (frozenIncr B hd H (gridPt t n i) (gridPt t n (i + 1))) :=
    (measurable_frozenIncr B hd hH.toHolderAdapted h0 h1 le_rfl h2).mono
      ((pathFiltration B).le_ambient _) le_rfl
  refine ⟨hm, memLp_eight_of_integrable_pow_eight hm.aestronglyMeasurable hb.1, ?_⟩
  have := hb.2
  rw [gridPt_succ_sub] at this
  exact this

/-- **`∑ Z(τᵢ) aᵢ → 0` almost surely**, `aᵢ` the frozen increments of `∫ σ dW`. -/
theorem ae_tendsto_sum_kitDoleansExp_mul_frozenIncr (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ range (n + 1),
      kitDoleansExp B (signatureSigma B hT ℓ) (gridPt t n i) ω *
        frozenIncr B hd (signatureSigma B hT ℓ) (gridPt t n i) (gridPt t n (i + 1)) ω)
      atTop (𝓝 0) := by
  obtain ⟨Cz, hCz0, hCz⟩ := exists_integral_kitDoleansExp_pow_eight_le B hd hT hw hℓ h3
  obtain ⟨K, hH⟩ := holderAdapted8_signatureSigma B hT hw hℓ t
  have hgT : ∀ n i, i ≤ n + 1 → gridPt t n i ∈ Set.Icc 0 T := fun n i hi =>
    ⟨gridPt_nonneg ht.1 n i, (gridPt_le ht.1 hi).trans ht.2⟩
  set CA : ℝ := 128 * 14 ^ 4 * gauss8Const * K with hCA
  set C0 : ℝ := 16 * (root4 Cz * root4 CA) ^ 2 * t ^ 4 with hC0
  refine ae_tendsto_zero_of_summable_integral_pow_four (b := fun n => C0 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun n => ?_) (fun n => ?_) ((summable_one_div_succ_pow one_lt_two).mul_left C0) (fun n => ?_)
  · refine Finset.measurable_sum _ fun i hi => ?_
    exact (measurable_kitDoleansExp B _ _).mul
      (frozenIncr_grid_bound B hd hH ht.1 n i (mem_range.mp hi)).1
  · refine integrable_pow_of_memLp_four (memLp_finsetSum _ fun i hi => ?_) le_rfl
    exact memLp_mul_four_of_eight (hCz _ (hgT n i (mem_range.mp hi).le)).1
      (frozenIncr_grid_bound B hd hH ht.1 n i (mem_range.mp hi)).2.1
  · have hb := integral_sum_mul_frozenIncr_pow_four_le B hd hH (τ := gridPt t n)
      (gridPt_nonneg ht.1 n 0) (gridPt_mono ht.1 n) (n + 1) (gridPt_le ht.1 le_rfl)
      (c := fun i => kitDoleansExp B (signatureSigma B hT ℓ) (gridPt t n i))
      (fun i _ => kitDoleansExp_adapted_path B _ (gridPt t n i)
        ⟨gridPt t n i, gridPt_nonneg ht.1 n i, le_rfl⟩)
      (fun i hi => (hCz _ (hgT n i hi.le)).1) (fun i hi => (hCz _ (hgT n i hi.le)).2)
    rw [sum_gridPt_sub_sq] at hb
    refine hb.trans (le_of_eq ?_)
    simp only [hC0]
    ring

/-- **`∑ aᵢ² → 0` almost surely** for the frozen increments of `∫ σ dW`. -/
theorem ae_tendsto_sum_frozenIncr_sq (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ range (n + 1),
      frozenIncr B hd (signatureSigma B hT ℓ) (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨K, hH⟩ := holderAdapted8_signatureSigma B hT hw hℓ t
  set a : ℕ → ℕ → Ω → ℝ := fun n i =>
    frozenIncr B hd (signatureSigma B hT ℓ) (gridPt t n i) (gridPt t n (i + 1)) with ha
  set CA : ℝ := 128 * 14 ^ 4 * gauss8Const * K with hCA
  have hfb := fun n i hi => frozenIncr_grid_bound B hd hH ht n i hi
  have hpt : ∀ n ω, (∑ i ∈ range (n + 1), a n i ω ^ 2) ^ 4 ≤
      ((n + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (n + 1), a n i ω ^ 8 := by
    intro n ω
    have hc := pow_sum_div_card_le_sum_pow (s := range (n + 1)) (f := fun i => a n i ω ^ 2)
      (fun i _ => sq_nonneg _) 3
    rw [card_range] at hc
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [div_le_iff₀ hpos] at hc
    calc (∑ i ∈ range (n + 1), a n i ω ^ 2) ^ 4 ≤
        (∑ i ∈ range (n + 1), (a n i ω ^ 2) ^ (3 + 1)) * ((n + 1 : ℕ) : ℝ) ^ 3 := by
          push_cast at hc ⊢; exact hc
      _ = _ := by
          rw [mul_comm]; congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
  have hdomI : ∀ n, Integrable (fun ω => ((n + 1 : ℕ) : ℝ) ^ 3 *
      ∑ i ∈ range (n + 1), a n i ω ^ 8) P := fun n =>
    (integrable_finsetSum _ fun i hi =>
      integrable_pow_of_memLp_eight (hfb n i (mem_range.mp hi)).2.1 le_rfl).const_mul _
  have hAm : ∀ n, Measurable (fun ω => ∑ i ∈ range (n + 1), a n i ω ^ 2) := fun n =>
    Finset.measurable_sum _ fun i hi => (hfb n i (mem_range.mp hi)).1.pow_const 2
  refine ae_tendsto_zero_of_summable_integral_pow_four
    (b := fun n => CA * t ^ 8 * (1 / ((n + 1 : ℕ) : ℝ) ^ 4))
    hAm (fun n => ?_) ((summable_one_div_succ_pow (by norm_num)).mul_left _) (fun n => ?_)
  · refine (hdomI n).mono' ((hAm n).pow_const 4).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt n ω
  · have hAi : Integrable (fun ω => (∑ i ∈ range (n + 1), a n i ω ^ 2) ^ 4) P :=
      (hdomI n).mono' ((hAm n).pow_const 4).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt n ω)
    calc ∫ ω, (∑ i ∈ range (n + 1), a n i ω ^ 2) ^ 4 ∂P
        ≤ ∫ ω, ((n + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (n + 1), a n i ω ^ 8 ∂P :=
          integral_mono hAi (hdomI n) (fun ω => hpt n ω)
      _ = ((n + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (n + 1), ∫ ω, a n i ω ^ 8 ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun i hi =>
            integrable_pow_of_memLp_eight (hfb n i (mem_range.mp hi)).2.1 le_rfl]
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (n + 1),
            CA * (t / ((n + 1 : ℕ) : ℝ)) ^ 8 := by
          gcongr with i hi
          exact (hfb n i (mem_range.mp hi)).2.2
      _ = CA * t ^ 8 * (1 / ((n + 1 : ℕ) : ℝ) ^ 4) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp

/-- **`∑ Z(τᵢ) σ(τᵢ)² ((ΔWᵢ)² - δ) → 0` almost surely.** -/
theorem ae_tendsto_sum_kitDoleansExp_mul_qvIncrR (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ range (n + 1),
      (kitDoleansExp B (signatureSigma B hT ℓ) (gridPt t n i) ω *
        signatureSigma B hT ℓ (gridPt t n i) ω ^ 2) *
        qvIncrR B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω)
      atTop (𝓝 0) := by
  obtain ⟨Ch, hCh0, hCh⟩ := exists_integral_kitDoleansExp_mul_sq_pow_four_le B hd hT hw hℓ h3
  obtain ⟨K, hH⟩ := holderAdapted8_signatureSigma B hT hw hℓ t
  have hgT : ∀ n i, i ≤ n + 1 → gridPt t n i ∈ Set.Icc 0 T := fun n i hi =>
    ⟨gridPt_nonneg ht.1 n i, (gridPt_le ht.1 hi).trans ht.2⟩
  set h : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    kitDoleansExp B (signatureSigma B hT ℓ) (gridPt t n i) ω *
      signatureSigma B hT ℓ (gridPt t n i) ω ^ 2 with hh
  have hhm : ∀ n i, i < n + 1 → Measurable[(pathFiltration B).σAlg (gridPt t n i)] (h n i) :=
    fun n i hi => (kitDoleansExp_adapted_path B _ (gridPt t n i)
      ⟨gridPt t n i, gridPt_nonneg ht.1 n i, le_rfl⟩).mul
      ((hH.meas _ (gridPt_nonneg ht.1 n i) (gridPt_le ht.1 hi.le)).pow_const 2)
  have hq := qvFourthConst_nonneg
  set C0 : ℝ := 16 * qvFourthConst * Ch * t ^ 4 with hC0
  refine ae_tendsto_zero_of_summable_integral_pow_four (b := fun n => C0 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun n => ?_) (fun n => ?_) ((summable_one_div_succ_pow one_lt_two).mul_left C0) (fun n => ?_)
  · refine Finset.measurable_sum _ fun i hi => ?_
    exact ((hhm n i (mem_range.mp hi)).mono ((pathFiltration B).le_ambient _) le_rfl).mul
      ((by fun_prop : Measurable (fun x : ℝ => x ^ 2 - (gridPt t n (i + 1) - gridPt t n i))).comp
        (measurable_wnnIncr B _ _ _))
  · refine integrable_pow_of_memLp_four (memLp_finsetSum _ fun i hi => ?_) le_rfl
    exact memLp_mul_qvIncrR B _ (gridPt_nonneg ht.1 n i) (gridPt_mono ht.1 n (Nat.le_succ i))
      (hhm n i (mem_range.mp hi)) (hCh _ (hgT n i (mem_range.mp hi).le)).1
  · have hb := integral_sum_mul_qvIncrR_pow_four_le B (kitDriver hd) (τ := gridPt t n)
      (gridPt_nonneg ht.1 n 0) (gridPt_mono ht.1 n) (n + 1) (h := h n) (hhm n)
      (fun i hi => (hCh _ (hgT n i hi.le)).1)
    refine hb.trans ?_
    have hs : ∑ i ∈ range (n + 1), Real.sqrt (∫ ω, h n i ω ^ 4 ∂P) *
        (gridPt t n (i + 1) - gridPt t n i) ^ 2 ≤
        Real.sqrt Ch * (t ^ 2 * (1 / ((n + 1 : ℕ) : ℝ))) := by
      rw [← sum_gridPt_sub_sq, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (hCh _ (hgT n i (mem_range.mp hi).le)).2) (sq_nonneg _)
    have hs0 : 0 ≤ ∑ i ∈ range (n + 1), Real.sqrt (∫ ω, h n i ω ^ 4 ∂P) *
        (gridPt t n (i + 1) - gridPt t n i) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc 16 * (Real.sqrt qvFourthConst * ∑ i ∈ range (n + 1), Real.sqrt (∫ ω, h n i ω ^ 4 ∂P) *
          (gridPt t n (i + 1) - gridPt t n i) ^ 2) ^ 2
        ≤ 16 * (Real.sqrt qvFourthConst * (Real.sqrt Ch * (t ^ 2 * (1 / ((n + 1 : ℕ) : ℝ))))) ^ 2 := by
          gcongr
      _ = C0 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hCh0, hC0]
          ring

end Inputs

end SignatureVolatility
