module

public import SignatureVolatility.ItoCalculusKit.ItoOrthogonal

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Freezing the integrand on a short interval, at order 8

For an adapted `L⁸`-Hölder integrand `H` and `0 ≤ u ≤ v ≤ t`,
`E (I_v - I_u - H_u (W_v - W_u))⁸ ≤ 128 · 14⁴ · c₈ · K · (v - u)⁸`
(`integral_kitItoIntRaw_sub_frozen_pow_eight_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Frozen8

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- Eighth-moment Hölder bound for a pair of times at distance `≤ δ`. -/
lemma root4_integral_sub_pow_eight_le (hH : HolderAdapted8 B H t K) {p q δ : ℝ} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpt : p ≤ t) (hqt : q ≤ t) (hδ : 0 ≤ δ) (hpq : |p - q| ≤ δ) :
    root4 (∫ ω, (H p ω - H q ω) ^ 8 ∂P) ≤ root4 K * δ := by
  have hK := hH.K_nonneg
  have h4 : (p - q) ^ 4 ≤ δ ^ 4 := by
    rw [← Even.pow_abs (by decide : Even 4)]; exact pow_le_pow_left₀ (abs_nonneg _) hpq 4
  have hhol : ∫ ω, (H p ω - H q ω) ^ 8 ∂P ≤ K * δ ^ 4 := by
    rcases le_total q p with hqp | hpq'
    · exact (hH.holder q p hq hqp hpt).trans (mul_le_mul_of_nonneg_left h4 hK)
    · have h := hH.holder p q hp hpq' hqt
      have heq : ∫ ω, (H p ω - H q ω) ^ 8 ∂P = ∫ ω, (H q ω - H p ω) ^ 8 ∂P := by
        congr 1; funext ω; ring
      rw [heq]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
      have : (q - p) ^ 4 = (p - q) ^ 4 := by ring
      rw [this]; exact h4
  calc root4 (∫ ω, (H p ω - H q ω) ^ 8 ∂P) ≤ root4 (K * δ ^ 4) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hhol)
    _ = root4 K * δ := by rw [root4_mul hK, root4_pow_four_self hδ]

/-- **Grid change at order 8**. -/
theorem integral_gridChange_le8 (hH : HolderAdapted8 B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    Integrable (fun ω => (unifRiemann B k H v N ω - unifRiemann B k H u N ω -
      offRiemann B k H u v N ω) ^ 8) P ∧
    ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 8 ∂P ≤
      (14 * root4 gauss8Const * (root4 K * (v / (N : ℝ)) * v)) ^ 4 := by
  have hv : 0 < v := hu.trans_lt huv
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΔ : 0 ≤ v / (N : ℝ) := (div_pos hv hNr).le
  have hH4 := hH.toHolderAdapted
  have hDprop : ∀ s, 0 ≤ s → s < v →
      (Measurable[(pathFiltration B).σAlg s] (gridDiff H u v N s) ∧
        MemLp (gridDiff H u v N s) 8 P) ∧
      root4 (∫ ω, gridDiff H u v N s ω ^ 8 ∂P) ≤ root4 K * (v / (N : ℝ)) := by
    intro s hs hsv
    obtain ⟨p, q, hp0, hps, hq0, hqs, hpq, hD⟩ := gridDiff_eq (H := H) hu huv hN hs hsv
    have hpt : p ≤ t := hps.trans (hsv.le.trans hvt)
    have hqt : q ≤ t := hqs.trans (hsv.le.trans hvt)
    have hfun : gridDiff H u v N s = fun ω => H p ω - H q ω := funext hD
    rw [hfun]
    refine ⟨⟨((hH.meas p hp0 hpt).mono ((pathFiltration B).mono hps) le_rfl).sub
      ((hH.meas q hq0 hqt).mono ((pathFiltration B).mono hqs) le_rfl),
      (hH.memLp p hp0 hpt).sub (hH.memLp q hq0 hqt)⟩, ?_⟩
    exact root4_integral_sub_pow_eight_le B hH hp0 hq0 hpt hqt hΔ hpq
  have hlim : ∀ ω, Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
      gridDiff H u v N ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω *
        wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
          (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop
      (𝓝 (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)) := by
    intro ω
    have h1 := tendsto_fineStepSum B k hv.le le_rfl N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) ω
    have h2 := tendsto_fineStepSum B k hu huv.le N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) ω
    have h3 := tendsto_fineStepSumOff B k hv hu huv.le le_rfl N
      (fun j => H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω) ω
    refine ((h1.sub h2).sub h3).congr fun M => ?_
    simp only [gridDiff, sub_mul, Finset.sum_sub_distrib]
  have hm : AEStronglyMeasurable (fun ω => unifRiemann B k H v N ω - unifRiemann B k H u N ω -
      offRiemann B k H u v N ω) P :=
    (((memLp_unifRiemann B k hv.le (hH4.mono hvt) hN).sub
      (memLp_unifRiemann B k hu (hH4.mono (huv.le.trans hvt)) hN)).sub
      (memLp_offRiemann B k hH4 hu huv.le hvt hN)).aestronglyMeasurable
  exact integral_pow_eight_le_of_fineSums B k hv (gridDiff H u v N)
    (fun s hs hsv => (hDprop s hs hsv).1) (fun s hs hsv => (hDprop s hs hsv).2) hm
    (ae_of_all _ hlim)

/-- **Off-grid sum minus the frozen term, at order 8.** -/
theorem integral_offRiemann_sub_frozen_pow_eight_le (hH : HolderAdapted8 B H t K) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    MemLp (fun ω => offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) 8 P ∧
    ∫ ω, (offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) ^ 8 ∂P ≤
      14 ^ 4 * gauss8Const * K * (v - u) ^ 8 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set Δ : ℝ := (v - u) / (N : ℝ) with hΔdef
  have hΔ : 0 ≤ Δ := div_nonneg (sub_nonneg.mpr huv) hNr.le
  set τ : ℕ → ℝ := fun j => u + (j : ℝ) * Δ with hτdef
  have hτmono : Monotone τ := by
    intro i j hij
    have hc : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    simp only [hτdef]
    nlinarith
  have hτN : τ N = v := by simp only [hτdef, hΔdef]; field_simp; ring
  have hmem : ∀ j < N, u ≤ τ j ∧ τ j ≤ v := fun j hj => offGrid_mem huv hN hj.le
  set h : ℕ → Ω → ℝ := fun j ω => H (τ j) ω - H u ω with hhdef
  have hmeas : ∀ j < N, Measurable[(pathFiltration B).σAlg (τ j)] (h j) := fun j hj =>
    (hH.meas _ (hu.trans (hmem j hj).1) ((hmem j hj).2.trans hvt)).sub
      ((hH.meas u hu (huv.trans hvt)).mono ((pathFiltration B).mono (hmem j hj).1) le_rfl)
  have hLp : ∀ j < N, MemLp (h j) 8 P := fun j hj =>
    (hH.memLp _ (hu.trans (hmem j hj).1) ((hmem j hj).2.trans hvt)).sub
      (hH.memLp u hu (huv.trans hvt))
  have heq : (fun ω => offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) =
      fun ω => ∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω := by
    funext ω
    have htel : ∑ j ∈ range N, wnnIncr B k (τ j) (τ (j + 1)) ω = wnnIncr B k u v ω := by
      simp only [wnnIncr]
      rw [Finset.sum_range_sub (fun j => B.Wnn (Real.toNNReal (τ j)) ω k), hτN]
      simp [hτdef]
    rw [← htel, Finset.mul_sum]
    unfold offRiemann
    rw [← Finset.sum_sub_distrib]
    simp only [hhdef, sub_mul]
    rfl
  have hL : MemLp (fun ω => ∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) 8 P := by
    have hs := memLp_finsetSum' (p := 8) (μ := P) (range N)
      (f := fun j ω => h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) fun j hj =>
        memLp_mul_wnnIncr_eight B k (hu.trans (hmem j (mem_range.mp hj)).1)
          (hτmono (Nat.le_succ j)) (hmeas j (mem_range.mp hj)) (hLp j (mem_range.mp hj))
    have hfun : (∑ j ∈ range N, fun ω => h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) =
        fun ω => ∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω := by
      funext ω; simp
    rwa [hfun] at hs
  have hI : ∫ ω, (offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) ^ 8 ∂P =
      ∫ ω, (∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ 8 ∂P := by
    congr 1; funext ω; rw [congrFun heq ω]
  refine ⟨heq ▸ hL, ?_⟩
  rw [hI]
  have hT := integral_transform_pow_eight_le B k (by simpa [hτdef] using hu) hτmono h N
    hmeas hLp
  refine hT.trans ?_
  have hg8 := root4_nonneg gauss8Const
  have hsum : ∑ j ∈ range N, root4 (∫ ω, h j ω ^ 8 ∂P) * (τ (j + 1) - τ j) ≤
      root4 K * (v - u) ^ 2 := by
    have hterm : ∀ j ∈ range N, root4 (∫ ω, h j ω ^ 8 ∂P) * (τ (j + 1) - τ j) ≤
        root4 K * (v - u) * Δ := by
      intro j hj
      have hj' := mem_range.mp hj
      have hstep : τ (j + 1) - τ j = Δ := by simp only [hτdef]; push_cast; ring
      rw [hstep]
      refine mul_le_mul_of_nonneg_right ?_ hΔ
      have habs : |τ j - u| ≤ v - u := by
        rw [abs_of_nonneg (by linarith [(hmem j hj').1])]; linarith [(hmem j hj').2]
      exact root4_integral_sub_pow_eight_le B hH (hu.trans (hmem j hj').1) hu
        ((hmem j hj').2.trans hvt) (huv.trans hvt) (sub_nonneg.mpr huv) habs
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hΔdef]
    field_simp
  have hK := hH.K_nonneg
  calc (14 * root4 gauss8Const *
        ∑ j ∈ range N, root4 (∫ ω, h j ω ^ 8 ∂P) * (τ (j + 1) - τ j)) ^ 4
      ≤ (14 * root4 gauss8Const * (root4 K * (v - u) ^ 2)) ^ 4 := by
        refine pow_le_pow_left₀ (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
          mul_nonneg (root4_nonneg _) (sub_nonneg.mpr (hτmono (Nat.le_succ j))))) ?_ 4
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 14 ^ 4 * gauss8Const * K * (v - u) ^ 8 := by
        rw [mul_pow, mul_pow, mul_pow, root4_pow_four gauss8Const_nonneg, root4_pow_four hK]
        ring

/-- **Freezing the integrand, at order 8**: `E (I_v - I_u - H_u ΔW)⁸ ≤ 128·14⁴·c₈·K·(v-u)⁸`. -/
theorem integral_kitItoIntRaw_sub_frozen_pow_eight_le (hd : 0 < d) (hH : HolderAdapted8 B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    Integrable (fun ω => (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B (kitDriver hd) u v ω) ^ 8) P ∧
    ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B (kitDriver hd) u v ω) ^ 8 ∂P ≤
        128 * 14 ^ 4 * gauss8Const * K * (v - u) ^ 8 := by
  rcases huv.eq_or_lt with rfl | hlt
  · simp [wnnIncr]
  set k := kitDriver hd
  have hv : 0 < v := hu.trans_lt hlt
  have hH4 := hH.toHolderAdapted
  have hIv := kitItoIntRaw_of_holderAdapted B hd hv.le (hH4.mono hvt)
  have hIu := kitItoIntRaw_of_holderAdapted B hd hu (hH4.mono (huv.trans hvt))
  have hW : MemLp (fun ω => H u ω * wnnIncr B k u v ω) 8 P :=
    memLp_mul_wnnIncr_eight B k hu huv (hH.meas u hu (huv.trans hvt)) (hH.memLp u hu (huv.trans hvt))
  have hg : AEStronglyMeasurable (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B k u v ω) P :=
    ((hIv.2.1.sub hIu.2.1).sub (hW.mono_exponent (by norm_num))).aestronglyMeasurable
  set f : ℕ → Ω → ℝ := fun n ω => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω - H u ω * wnnIncr B k u v ω with hfdef
  have hfL : ∀ n : ℕ, MemLp (f n) 8 P := fun n =>
    ((memLp_unifRiemann_eight B k hv.le (hH.mono hvt) n.succ_pos).sub
      (memLp_unifRiemann_eight B k hu (hH.mono (huv.trans hvt)) n.succ_pos)).sub hW
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => f n ω) atTop
      (𝓝 (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω - H u ω * wnnIncr B k u v ω)) := by
    filter_upwards [hIv.1, hIu.1] with ω h1 h2
    exact (h1.sub h2).sub tendsto_const_nhds
  set G : ℕ → ℝ := fun n => (14 * root4 gauss8Const *
    (root4 K * (v / ((n + 1 : ℕ) : ℝ)) * v)) ^ 4 with hGdef
  set T : ℝ := 14 ^ 4 * gauss8Const * K * (v - u) ^ 8 with hTdef
  have hb : ∀ n, ∫ ω, f n ω ^ 8 ∂P ≤ 128 * G n + 128 * T := by
    intro n
    obtain ⟨hA, hA'⟩ := integral_gridChange_le8 B k hH hu hlt hvt n.succ_pos
    obtain ⟨hO, hO'⟩ := integral_offRiemann_sub_frozen_pow_eight_le B k hH hu huv hvt n.succ_pos
    have hOi := integrable_pow_of_memLp_eight hO (k := 8) le_rfl
    have hpt : (fun ω => f n ω ^ 8) ≤ fun ω =>
        128 * (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω) ^ 8 +
        128 * (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 8 := by
      intro ω
      have h := add_pow_eight_le_conv
        (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω)
        (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω)
      have he : f n ω = (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω) +
          (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) := by
        simp only [hfdef]; ring
      simp only
      rw [he]; exact h
    calc ∫ ω, f n ω ^ 8 ∂P ≤ ∫ ω,
          (128 * (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
            offRiemann B k H u v (n + 1) ω) ^ 8 +
          128 * (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 8) ∂P :=
          integral_mono (integrable_pow_of_memLp_eight (hfL n) (k := 8) le_rfl)
            ((hA.const_mul 128).add (hOi.const_mul 128)) hpt
      _ = 128 * (∫ ω, (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
            offRiemann B k H u v (n + 1) ω) ^ 8 ∂P) +
          128 * ∫ ω, (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 8 ∂P := by
          rw [integral_add (hA.const_mul 128) (hOi.const_mul 128), integral_const_mul,
            integral_const_mul]
      _ ≤ 128 * G n + 128 * T := by
          have hA'' : _ ≤ G n := hA'
          linarith
  have hbc : Tendsto (fun n => 128 * G n + 128 * T) atTop (𝓝 (128 * T)) := by
    have h0 : Tendsto (fun n : ℕ => v / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
      exact h.congr fun n => by simp
    have h1 := ((((tendsto_const_nhds (x := root4 K)).mul h0).mul_const v).const_mul
      (14 * root4 gauss8Const)).pow 4
    have h2 := (h1.const_mul 128).add_const (128 * T)
    convert h2 using 2
    simp
  have hres := integral_pow_eight_le_of_tendsto hg
    (fun n => (hfL n).aestronglyMeasurable.aemeasurable) hlim
    (fun n => integrable_pow_of_memLp_eight (hfL n) (k := 8) le_rfl) hb hbc
  refine ⟨hres.1, hres.2.trans (le_of_eq ?_)⟩
  simp only [hTdef]; ring

end Frozen8

end SignatureVolatility
