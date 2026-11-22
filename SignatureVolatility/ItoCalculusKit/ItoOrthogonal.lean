module

public import SignatureVolatility.ItoCalculusKit.GridChange

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Orthogonality of raw Itô increments to the past

* `integral_kitItoIntRaw_sub_offRiemann_le`: `E (I_v - I_u - R_{[u,v]}^N)⁴ ≤ C / N²`;
* `integral_mul_offRiemann_eq_zero`: `E[g · R_{[u,v]}^N] = 0` for `𝓕_u`-measurable `g ∈ L²`;
* `integral_mul_kitItoIntRaw_sub_eq_zero`: `E[g · (I_v - I_u)] = 0` for `𝓕_u`-measurable `g ∈ L²`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- Products of two `L²` functions are integrable. -/
lemma integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine ((hf.integrable_sq.add hg.integrable_sq).div_const 2).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  show |f ω| * |g ω| ≤ (f ω ^ 2 + g ω ^ 2) / 2
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]

omit [IsProbabilityMeasure P] in
/-- **Cauchy–Schwarz.** -/
lemma abs_integral_mul_le_sqrt {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (μ := P) (f := fun ω => |f ω|)
    (g := fun ω => |g ω|) (ae_of_all _ fun ω => abs_nonneg _) (ae_of_all _ fun ω => abs_nonneg _)
    (by rw [h2]; simpa [Real.norm_eq_abs] using hf.norm)
    (by rw [h2]; simpa [Real.norm_eq_abs] using hg.norm)
  have hsq : ∀ x : ℝ, |x| ^ (2 : ℝ) = x ^ 2 := fun x => by rw [Real.rpow_two, sq_abs]
  simp only [hsq, ← Real.sqrt_eq_rpow] at h
  calc |∫ ω, f ω * g ω ∂P| ≤ ∫ ω, |f ω * g ω| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, |f ω| * |g ω| ∂P := by simp_rw [abs_mul]
    _ ≤ _ := h

lemma pow_four_add3_le (x y z : ℝ) : (x + y + z) ^ 4 ≤ 27 * (x ^ 4 + y ^ 4 + z ^ 4) := by
  have h1 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≤ 3 * (x ^ 4 + y ^ 4 + z ^ 4) := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (x ^ 2 - z ^ 2)]
  calc (x + y + z) ^ 4 = ((x + y + z) ^ 2) ^ 2 := by ring
    _ ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = 9 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by ring
    _ ≤ 9 * (3 * (x ^ 4 + y ^ 4 + z ^ 4)) := by linarith
    _ = 27 * (x ^ 4 + y ^ 4 + z ^ 4) := by ring

lemma offGrid_mem {u v : ℝ} (huv : u ≤ v) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j ≤ N) :
    u ≤ u + (j : ℝ) * ((v - u) / (N : ℝ)) ∧ u + (j : ℝ) * ((v - u) / (N : ℝ)) ≤ v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΔ : 0 ≤ (v - u) / (N : ℝ) := div_nonneg (sub_nonneg.mpr huv) hNr.le
  refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hΔ), ?_⟩
  have : (j : ℝ) * ((v - u) / (N : ℝ)) ≤ (N : ℝ) * ((v - u) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hΔ
  have h2 : (N : ℝ) * ((v - u) / (N : ℝ)) = v - u := by field_simp
  linarith

lemma offGrid_step {u v : ℝ} (huv : u ≤ v) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    u + (j : ℝ) * ((v - u) / (N : ℝ)) ≤ u + ((j + 1 : ℕ) : ℝ) * ((v - u) / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΔ : 0 ≤ (v - u) / (N : ℝ) := div_nonneg (sub_nonneg.mpr huv) hNr.le
  have : (j : ℝ) * ((v - u) / (N : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) * ((v - u) / (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) hΔ
  linarith

section Orthogonal

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

lemma memLp_offRiemann (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) : MemLp (offRiemann B k H u v N) 4 P := by
  have h := memLp_finsetSum' (p := 4) (μ := P) (range N)
    (f := fun j ω => H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω *
      wnnIncr B k (u + (j : ℝ) * ((v - u) / (N : ℝ)))
        (u + ((j + 1 : ℕ) : ℝ) * ((v - u) / (N : ℝ))) ω)
    fun j hj => by
      obtain ⟨h0, h1⟩ := offGrid_mem huv hN (Finset.mem_range.mp hj).le
      exact memLp_mul_wnnIncr B k (hu.trans h0) (offGrid_step huv hN j)
        (hH.meas _ (hu.trans h0) (h1.trans hvt)) (hH.memLp _ (hu.trans h0) (h1.trans hvt))
  have hfun : (∑ j ∈ range N, fun ω => H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω *
      wnnIncr B k (u + (j : ℝ) * ((v - u) / (N : ℝ)))
        (u + ((j + 1 : ℕ) : ℝ) * ((v - u) / (N : ℝ))) ω) = offRiemann B k H u v N := by
    funext ω; simp [offRiemann]
  rwa [hfun] at h

/-- **`L⁴` rate of the off-grid sums towards the raw increment.** -/
theorem integral_kitItoIntRaw_sub_offRiemann_le (hd : 0 < d) (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    MemLp (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      offRiemann B (kitDriver hd) H u v N ω) 4 P ∧
    ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      offRiemann B (kitDriver hd) H u v N ω) ^ 4 ∂P ≤
        27 * gaussFourthConst * K * (144 * v ^ 4 + 128 * u ^ 4) / (N : ℝ) ^ 2 := by
  set k := kitDriver hd
  have hv : 0 < v := hu.trans_lt huv
  have hHv := hH.mono hvt
  have hHu := hH.mono (huv.le.trans hvt)
  obtain ⟨ha, ha'⟩ := integral_unifRiemann_sub_kitItoIntRaw_le B hd hv.le hHv hN
  obtain ⟨hb, hb'⟩ := integral_unifRiemann_sub_kitItoIntRaw_le B hd hu hHu hN
  obtain ⟨hc, hc'⟩ := integral_gridChange_le B k hH hu huv hvt hN
  have hIv := (kitItoIntRaw_of_holderAdapted B hd hv.le hHv).2.1
  have hIu := (kitItoIntRaw_of_holderAdapted B hd hu hHu).2.1
  have hL : MemLp (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      offRiemann B k H u v N ω) 4 P :=
    (hIv.sub hIu).sub (memLp_offRiemann B k hH hu huv.le hvt hN)
  refine ⟨hL, ?_⟩
  have hpt : (fun ω => (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
      offRiemann B k H u v N ω) ^ 4) ≤ fun ω =>
      27 * ((unifRiemann B k H v N ω - kitItoIntRaw B H v ω) ^ 4 +
        (unifRiemann B k H u N ω - kitItoIntRaw B H u ω) ^ 4 +
        (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 4) := by
    intro ω
    have h := pow_four_add3_le (-(unifRiemann B k H v N ω - kitItoIntRaw B H v ω))
      (unifRiemann B k H u N ω - kitItoIntRaw B H u ω)
      (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)
    calc _ = (-(unifRiemann B k H v N ω - kitItoIntRaw B H v ω) +
          (unifRiemann B k H u N ω - kitItoIntRaw B H u ω) +
          (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)) ^ 4 := by
          ring
      _ ≤ _ := h
      _ = _ := by ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc _ ≤ ∫ ω, 27 * ((unifRiemann B k H v N ω - kitItoIntRaw B H v ω) ^ 4 +
        (unifRiemann B k H u N ω - kitItoIntRaw B H u ω) ^ 4 +
        (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 4) ∂P :=
        integral_mono (integrable_pow_of_memLp_four hL (k := 4) le_rfl)
          (((ha.add hb).add hc).const_mul 27) hpt
    _ = 27 * ((∫ ω, (unifRiemann B k H v N ω - kitItoIntRaw B H v ω) ^ 4 ∂P) +
        (∫ ω, (unifRiemann B k H u N ω - kitItoIntRaw B H u ω) ^ 4 ∂P) +
        ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω -
          offRiemann B k H u v N ω) ^ 4 ∂P) := by
        have hab : Integrable (fun ω => (unifRiemann B k H v N ω - kitItoIntRaw B H v ω) ^ 4 +
            (unifRiemann B k H u N ω - kitItoIntRaw B H u ω) ^ 4) P := ha.add hb
        rw [integral_const_mul, integral_add hab hc, integral_add ha hb]
    _ ≤ 27 * (8 * (16 * gaussFourthConst * K * v ^ 4 / (N : ℝ) ^ 2) +
        8 * (16 * gaussFourthConst * K * u ^ 4 / (N : ℝ) ^ 2) +
        16 * gaussFourthConst * (Real.sqrt K * (v / (N : ℝ)) * v) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hH.K_nonneg]
        field_simp
        ring

/-- **The off-grid sum is orthogonal to the past.** -/
theorem integral_mul_offRiemann_eq_zero (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {g : Ω → ℝ}
    (hg : Measurable[(pathFiltration B).σAlg u] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * offRiemann B k H u v N ω ∂P = 0 := by
  unfold offRiemann
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨h0, h1⟩ := offGrid_mem huv hN (Finset.mem_range.mp hj).le
    have hstep := offGrid_step huv hN j
    have hgm : Measurable[(pathFiltration B).σAlg (u + (j : ℝ) * ((v - u) / (N : ℝ)))]
        (fun ω => g ω * H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω) :=
      (hg.mono ((pathFiltration B).mono h0) le_rfl).mul
        (hH.meas _ (hu.trans h0) (h1.trans hvt))
    have hI := (indepFun_pathFiltration_wnnIncr B k hstep hgm).integral_fun_mul_eq_mul_integral
      (hgm.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (measurable_wnnIncr B k _ _).aestronglyMeasurable
    have hmean := (hasLaw_wnnIncr B k (hu.trans h0) hstep).integral_eq
    rw [integral_id_gaussianReal] at hmean
    rw [hmean, mul_zero] at hI
    rw [← hI]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    ring
  · intro j hj
    obtain ⟨h0, h1⟩ := offGrid_mem huv hN (Finset.mem_range.mp hj).le
    have hξ := memLp_mul_wnnIncr B k (hu.trans h0) (offGrid_step huv hN j)
      (hH.meas _ (hu.trans h0) (h1.trans hvt)) (hH.memLp _ (hu.trans h0) (h1.trans hvt))
    exact integrable_mul_of_memLp_two hg2 (hξ.mono_exponent (by norm_num))

/-- **Raw Itô increments are orthogonal to the past.** -/
theorem integral_mul_kitItoIntRaw_sub_eq_zero (hd : 0 < d) (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) {g : Ω → ℝ}
    (hg : Measurable[(pathFiltration B).σAlg u] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ∂P = 0 := by
  rcases huv.eq_or_lt with rfl | huv'
  · simp
  set C : ℝ := 27 * gaussFourthConst * K * (144 * v ^ 4 + 128 * u ^ 4) with hC
  set A : ℝ := Real.sqrt (∫ ω, g ω ^ 2 ∂P) with hA
  have hbound : ∀ N : ℕ, 0 < N → |∫ ω, g ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ∂P|
      ≤ A * Real.sqrt (Real.sqrt C / (N : ℝ)) := by
    intro N hN
    obtain ⟨hL, hle⟩ := integral_kitItoIntRaw_sub_offRiemann_le B hd hH hu huv' hvt hN
    have hoff := memLp_offRiemann B (kitDriver hd) hH hu huv hvt hN
    have hY2 := hL.mono_exponent (p := 2) (by norm_num)
    have hsplit : ∫ ω, g ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ∂P =
        (∫ ω, g ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
          offRiemann B (kitDriver hd) H u v N ω) ∂P) +
        ∫ ω, g ω * offRiemann B (kitDriver hd) H u v N ω ∂P := by
      rw [← integral_add (integrable_mul_of_memLp_two hg2 hY2)
        (integrable_mul_of_memLp_two hg2 (hoff.mono_exponent (by norm_num)))]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      ring
    rw [hsplit, integral_mul_offRiemann_eq_zero B (kitDriver hd) hH hu huv hvt hN hg hg2,
      add_zero]
    refine (abs_integral_mul_le_sqrt hg2 hY2).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    have h1 := sq_integral_sq_le_integral_pow_four hL
    have hnn : 0 ≤ ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω -
        offRiemann B (kitDriver hd) H u v N ω) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    have h2 := Real.abs_le_sqrt (h1.trans hle)
    rw [abs_of_nonneg hnn, Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)] at h2
    exact h2
  have ht : Tendsto (fun M : ℕ => A * Real.sqrt (Real.sqrt C / ((M + 1 : ℕ) : ℝ))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := Real.sqrt C)).div_atTop h1
    have h3 := ((Real.continuous_sqrt.tendsto 0).comp h2).const_mul A
    rw [Real.sqrt_zero, mul_zero] at h3
    exact h3
  exact abs_nonpos_iff.mp (ge_of_tendsto' ht fun M => hbound (M + 1) M.succ_pos)

end Orthogonal

end SignatureVolatility
