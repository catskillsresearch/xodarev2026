module

public import SignatureVolatility.ItoCalculusKit.ItoOrthogonal

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Freezing the integrand on a short interval, at order 4

For an adapted `L⁴`-Hölder integrand `H` and `0 ≤ u ≤ v ≤ t`,
`E (I_v - I_u - H_u (W_v - W_u))⁴ ≤ 128 · c₄ · K · (v - u)⁴`
(`integral_kitItoIntRaw_sub_frozen_pow_four_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Frozen4

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

lemma add_pow_four_le_frozen (a b : ℝ) : (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg ((a - b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b),
    sq_nonneg (a - b)]

/-- Off-grid Riemann sum minus the frozen term, fourth moment. -/
theorem integral_offRiemann_sub_frozen_pow_four_le (hH : HolderAdapted B H t K) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    MemLp (fun ω => offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) 4 P ∧
    ∫ ω, (offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) ^ 4 ∂P ≤
      16 * gaussFourthConst * K * (v - u) ^ 4 := by
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
  have hLp : ∀ j < N, MemLp (h j) 4 P := fun j hj =>
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
  have hL : MemLp (fun ω => ∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) 4 P := by
    have hs := memLp_finsetSum' (p := 4) (μ := P) (range N)
      (f := fun j ω => h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) fun j hj =>
        memLp_mul_wnnIncr B k (hu.trans (hmem j (mem_range.mp hj)).1)
          (hτmono (Nat.le_succ j)) (hmeas j (mem_range.mp hj)) (hLp j (mem_range.mp hj))
    have hfun : (∑ j ∈ range N, fun ω => h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) =
        fun ω => ∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω := by
      funext ω; simp
    rwa [hfun] at hs
  have hI : ∫ ω, (offRiemann B k H u v N ω - H u ω * wnnIncr B k u v ω) ^ 4 ∂P =
      ∫ ω, (∑ j ∈ range N, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ 4 ∂P := by
    congr 1; funext ω; rw [congrFun heq ω]
  refine ⟨heq ▸ hL, ?_⟩
  rw [hI]
  have hT := integral_transform_pow_four_le B k (by simpa [hτdef] using hu) hτmono h N
    hmeas hLp
  refine hT.trans ?_
  have hsum : ∑ j ∈ range N, Real.sqrt (∫ ω, h j ω ^ 4 ∂P) * (τ (j + 1) - τ j) ≤
      Real.sqrt K * (v - u) ^ 2 := by
    have hterm : ∀ j ∈ range N, Real.sqrt (∫ ω, h j ω ^ 4 ∂P) * (τ (j + 1) - τ j) ≤
        Real.sqrt K * (v - u) * Δ := by
      intro j hj
      have hj' := mem_range.mp hj
      have hstep : τ (j + 1) - τ j = Δ := by simp only [hτdef]; push_cast; ring
      rw [hstep]
      refine mul_le_mul_of_nonneg_right ?_ hΔ
      have habs : |τ j - u| ≤ v - u := by
        rw [abs_of_nonneg (by linarith [(hmem j hj').1])]; linarith [(hmem j hj').2]
      exact sqrt_integral_sub_pow_four_le B hH (hu.trans (hmem j hj').1) hu
        ((hmem j hj').2.trans hvt) (huv.trans hvt) (sub_nonneg.mpr huv) habs
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hΔdef]
    field_simp
  have hK := hH.K_nonneg
  calc 16 * gaussFourthConst *
        (∑ j ∈ range N, Real.sqrt (∫ ω, h j ω ^ 4 ∂P) * (τ (j + 1) - τ j)) ^ 2
      ≤ 16 * gaussFourthConst * (Real.sqrt K * (v - u) ^ 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by have := gaussFourthConst_nonneg; positivity)
        refine pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
          mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (hτmono (Nat.le_succ j)))) hsum 2
    _ = 16 * gaussFourthConst * K * (v - u) ^ 4 := by
        rw [mul_pow, Real.sq_sqrt hK]; ring

/-- **Freezing the integrand, at order 4**: `E (I_v - I_u - H_u ΔW)⁴ ≤ 128·c₄·K·(v-u)⁴`. -/
theorem integral_kitItoIntRaw_sub_frozen_pow_four_le (hd : 0 < d) (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    Integrable (fun ω => (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B (kitDriver hd) u v ω) ^ 4) P ∧
    ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B (kitDriver hd) u v ω) ^ 4 ∂P ≤
        128 * gaussFourthConst * K * (v - u) ^ 4 := by
  rcases huv.eq_or_lt with rfl | hlt
  · simp [wnnIncr]
  set k := kitDriver hd
  have hv : 0 < v := hu.trans_lt hlt
  have hIv := kitItoIntRaw_of_holderAdapted B hd hv.le (hH.mono hvt)
  have hIu := kitItoIntRaw_of_holderAdapted B hd hu (hH.mono (huv.trans hvt))
  have hW : MemLp (fun ω => H u ω * wnnIncr B k u v ω) 4 P :=
    memLp_mul_wnnIncr B k hu huv (hH.meas u hu (huv.trans hvt)) (hH.memLp u hu (huv.trans hvt))
  have hg : AEStronglyMeasurable (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      H u ω * wnnIncr B k u v ω) P :=
    ((hIv.2.1.sub hIu.2.1).sub hW).aestronglyMeasurable
  set f : ℕ → Ω → ℝ := fun n ω => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω - H u ω * wnnIncr B k u v ω with hfdef
  have hfL : ∀ n : ℕ, MemLp (f n) 4 P := fun n =>
    ((memLp_unifRiemann B k hv.le (hH.mono hvt) n.succ_pos).sub
      (memLp_unifRiemann B k hu (hH.mono (huv.trans hvt)) n.succ_pos)).sub hW
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => f n ω) atTop
      (𝓝 (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω - H u ω * wnnIncr B k u v ω)) := by
    filter_upwards [hIv.1, hIu.1] with ω h1 h2
    exact (h1.sub h2).sub tendsto_const_nhds
  set G : ℕ → ℝ := fun n => 16 * gaussFourthConst *
    (Real.sqrt K * (v / ((n + 1 : ℕ) : ℝ)) * v) ^ 2 with hGdef
  set T : ℝ := 16 * gaussFourthConst * K * (v - u) ^ 4 with hTdef
  have hb : ∀ n, ∫ ω, f n ω ^ 4 ∂P ≤ 8 * G n + 8 * T := by
    intro n
    obtain ⟨hA, hA'⟩ := integral_gridChange_le B k hH hu hlt hvt n.succ_pos
    obtain ⟨hO, hO'⟩ := integral_offRiemann_sub_frozen_pow_four_le B k hH hu huv hvt n.succ_pos
    have hOi := integrable_pow_of_memLp_four hO (k := 4) le_rfl
    have hpt : (fun ω => f n ω ^ 4) ≤ fun ω =>
        8 * (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω) ^ 4 +
        8 * (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 4 := by
      intro ω
      have h := add_pow_four_le_frozen
        (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω)
        (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω)
      have he : f n ω = (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
          offRiemann B k H u v (n + 1) ω) +
          (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) := by
        simp only [hfdef]; ring
      simp only
      rw [he]; exact h
    calc ∫ ω, f n ω ^ 4 ∂P ≤ ∫ ω,
          (8 * (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
            offRiemann B k H u v (n + 1) ω) ^ 4 +
          8 * (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 4) ∂P :=
          integral_mono (integrable_pow_of_memLp_four (hfL n) (k := 4) le_rfl)
            ((hA.const_mul 8).add (hOi.const_mul 8)) hpt
      _ = 8 * (∫ ω, (unifRiemann B k H v (n + 1) ω - unifRiemann B k H u (n + 1) ω -
            offRiemann B k H u v (n + 1) ω) ^ 4 ∂P) +
          8 * ∫ ω, (offRiemann B k H u v (n + 1) ω - H u ω * wnnIncr B k u v ω) ^ 4 ∂P := by
          rw [integral_add (hA.const_mul 8) (hOi.const_mul 8), integral_const_mul,
            integral_const_mul]
      _ ≤ 8 * G n + 8 * T := by
          have hA'' : _ ≤ G n := hA'
          linarith
  have hbc : Tendsto (fun n => 8 * G n + 8 * T) atTop (𝓝 (8 * T)) := by
    have h0 : Tendsto (fun n : ℕ => v / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
      exact h.congr fun n => by simp
    have h1 := ((((tendsto_const_nhds (x := Real.sqrt K)).mul h0).mul_const v).pow 2).const_mul
      (16 * gaussFourthConst)
    have h2 := (h1.const_mul 8).add_const (8 * T)
    convert h2 using 2
    simp
  have hres := integral_pow_four_le_of_tendsto hg
    (fun n => (hfL n).aestronglyMeasurable.aemeasurable) hlim
    (fun n => integrable_pow_of_memLp_four (hfL n) (k := 4) le_rfl) hb hbc
  refine ⟨hres.1, hres.2.trans (le_of_eq ?_)⟩
  simp only [hTdef]; ring

end Frozen4

end SignatureVolatility
