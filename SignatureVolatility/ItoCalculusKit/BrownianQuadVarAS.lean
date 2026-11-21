module

public import SignatureVolatility.ItoCalculusKit.FourthMoment
public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

noncomputable section

namespace SignatureVolatility

/-!
# Almost-sure quadratic variation of Brownian motion along uniform grids

For the uniform grids `t·j/(n+1)` used by `itoRiemann_process`, any block of centred squared
increments `∑_{j ∈ sₙ} ((ΔW_j)² - t/(n+1))`, `sₙ ⊆ {0,…,n}`, converges to `0` **almost surely along
the full sequence** `n → ∞` (fourth moments are `O(n⁻²)`, hence summable). Countably many blocks
give the pathwise Föllmer hypothesis `ae_tendsto_qvBlocks`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Gaussian moments of `x² - v` under `N(0, v)` -/

/-- `𝔼[(G² - 1)⁴]` for a standard Gaussian `G` (equal to `60`; only finiteness is used). -/
def qvFourthConst : ℝ := ∫ y, (y ^ 2 - 1) ^ 4 ∂(gaussianReal 0 1)

private lemma sub_pow_four_le (a b : ℝ) : (a - b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg ((a + b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2)]

lemma memLp_sq_sub_gaussianReal (v : ℝ≥0) :
    MemLp (fun x : ℝ => x ^ 2 - (v : ℝ)) 4 (gaussianReal 0 v) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2 - (v : ℝ)) (gaussianReal 0 v) :=
    (by fun_prop : Measurable fun x : ℝ => x ^ 2 - (v : ℝ)).aestronglyMeasurable
  have h8 : Integrable (fun x : ℝ => ‖x‖ ^ 8) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) ((8 : ℕ) : ℝ≥0∞) (by simp)).integrable_norm_pow
      (by norm_num)
  have h4 : MemLp (fun x : ℝ => x ^ 2 - (v : ℝ)) ((4 : ℕ) : ℝ≥0∞) (gaussianReal 0 v) := by
    rw [← integrable_norm_rpow_iff hmeas (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    refine Integrable.mono' (g := fun x : ℝ => 8 * ‖x‖ ^ 8 + 8 * (v : ℝ) ^ 4)
      ((h8.const_mul 8).add (integrable_const _)) (hmeas.norm.pow 4) (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs, abs_pow, abs_abs]
    have h1 : |x ^ 2 - (v : ℝ)| ^ 4 = (x ^ 2 - (v : ℝ)) ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    have h2 : |x| ^ 8 = (x ^ 2) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
      ring
    rw [h1, h2]
    exact sub_pow_four_le _ _
  exact_mod_cast h4

lemma integral_sq_sub_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ∂(gaussianReal 0 v) = 0 := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((2 : ℕ) : ℝ≥0∞) (by simp)).integrable_norm_pow
      (by norm_num)
    simpa using h
  rw [integral_sub h2 (integrable_const _), integral_const]
  simp only [id_eq] at h_var
  simp [h_var]

lemma integral_sq_sub_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ^ 4 ∂(gaussianReal 0 v) = qvFourthConst * (v : ℝ) ^ 4 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ y : ℝ, ((Real.sqrt v * y) ^ 2 - (v : ℝ)) ^ 4 = (v : ℝ) ^ 4 * (y ^ 2 - 1) ^ 4 := by
    intro y
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, qvFourthConst, mul_comm]

/-! ## Brownian increments on the `ℝ`-time grid -/

/-- Law of a Brownian increment in the `toNNReal` reindexing. -/
lemma hasLaw_wnnIncr (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    HasLaw (fun ω => wnnIncr B k a b ω) (gaussianReal 0 (Real.toNNReal (b - a))) P := by
  have h := (B.isBrownian k).toIsPreBrownianReal.hasLaw_sub (Real.toNNReal b) (Real.toNNReal a)
  have hv : nndist (Real.toNNReal b).1 (Real.toNNReal a).1 = Real.toNNReal (b - a) := by
    ext
    simp only [coe_nndist, Real.dist_eq]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab)]
    change |((Real.toNNReal b : ℝ≥0) : ℝ) - ((Real.toNNReal a : ℝ≥0) : ℝ)| = b - a
    rw [Real.coe_toNNReal _ (ha.trans hab), Real.coe_toNNReal _ ha, abs_of_nonneg (sub_nonneg.mpr hab)]
  rw [hv] at h
  exact h

/-- Centred squared increment on the uniform grid `j ↦ j·t/(n+1)`. -/
def qvIncr (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  (wnnIncr B k ((j : ℝ) * (t / ((n : ℝ) + 1))) (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) ω) ^ 2 -
    t / ((n : ℝ) + 1)

lemma measurable_qvIncr (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) (n j : ℕ) :
    Measurable (qvIncr B k t n j) :=
  ((measurable_wnnIncr B k _ _).pow_const 2).sub measurable_const

lemma iIndepFun_qvIncr (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    iIndepFun (fun j : ℕ => qvIncr B k t n j) P := by
  have hΔ : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht (by positivity)
  have hmono : Monotone fun j : ℕ => Real.toNNReal ((j : ℝ) * (t / ((n : ℝ) + 1))) := by
    intro i j hij
    exact Real.toNNReal_le_toNNReal
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hΔ)
  have h := ((B.isBrownian k).toIsPreBrownianReal.hasIndepIncrements.nat hmono).comp
    (fun _ x => x ^ 2 - t / ((n : ℝ) + 1)) (fun _ => by fun_prop)
  convert h using 2 with j
  funext ω
  simp [qvIncr, wnnIncr]

lemma hasLaw_gridIncr (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t) (n j : ℕ) :
    HasLaw (fun ω => wnnIncr B k ((j : ℝ) * (t / ((n : ℝ) + 1)))
      (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) ω)
      (gaussianReal 0 (Real.toNNReal (t / ((n : ℝ) + 1)))) P := by
  have hΔ : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht (by positivity)
  have h := hasLaw_wnnIncr B k (a := (j : ℝ) * (t / ((n : ℝ) + 1)))
    (b := ((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith) hΔ)
  have hsub : ((j : ℝ) + 1) * (t / ((n : ℝ) + 1)) - (j : ℝ) * (t / ((n : ℝ) + 1)) =
      t / ((n : ℝ) + 1) := by ring
  rwa [hsub] at h

lemma memLp_qvIncr (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t) (n j : ℕ) :
    MemLp (qvIncr B k t n j) 4 P := by
  have hΔ : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht (by positivity)
  have h := (hasLaw_gridIncr B k ht n j).memLp_comp
    (memLp_sq_sub_gaussianReal (Real.toNNReal (t / ((n : ℝ) + 1))))
  rw [Real.coe_toNNReal _ hΔ] at h
  exact h

lemma integral_qvIncr (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t) (n j : ℕ) :
    ∫ ω, qvIncr B k t n j ω ∂P = 0 := by
  have hΔ : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht (by positivity)
  have h := (hasLaw_gridIncr B k ht n j).integral_comp
    (f := fun x : ℝ => x ^ 2 - ((Real.toNNReal (t / ((n : ℝ) + 1)) : ℝ≥0) : ℝ))
    (by fun_prop : Measurable _).aestronglyMeasurable
  rw [integral_sq_sub_gaussianReal, Real.coe_toNNReal _ hΔ] at h
  exact h

lemma integral_qvIncr_pow_four (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (n j : ℕ) :
    ∫ ω, qvIncr B k t n j ω ^ 4 ∂P = qvFourthConst * (t / ((n : ℝ) + 1)) ^ 4 := by
  have hΔ : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht (by positivity)
  have h := (hasLaw_gridIncr B k ht n j).integral_comp
    (f := fun x : ℝ => (x ^ 2 - ((Real.toNNReal (t / ((n : ℝ) + 1)) : ℝ≥0) : ℝ)) ^ 4)
    (by fun_prop : Measurable _).aestronglyMeasurable
  rw [integral_sq_sub_pow_four_gaussianReal, Real.coe_toNNReal _ hΔ] at h
  exact h

/-- **Almost-sure block quadratic variation.** For any blocks `s n` with at most `n + 1` indices,
`∑_{j ∈ s n} ((ΔW_j)² - t/(n+1)) → 0` almost surely along the full sequence. -/
theorem ae_tendsto_qvBlock (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (s : ℕ → Finset ℕ) (hs : ∀ n, (s n).card ≤ n + 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ j ∈ s n, qvIncr B k t n j ω) atTop (𝓝 0) := by
  have hLp : ∀ n, MemLp (fun ω => ∑ j ∈ s n, qvIncr B k t n j ω) 4 P := fun n => by
    have h := memLp_finsetSum' (p := 4) (μ := P) (s n) fun j _ => memLp_qvIncr B k ht n j
    have hfun : (∑ j ∈ s n, qvIncr B k t n j) = fun ω => ∑ j ∈ s n, qvIncr B k t n j ω := by
      funext ω; simp
    rwa [hfun] at h
  have hC : 0 ≤ qvFourthConst := integral_nonneg fun y => by positivity
  refine ae_tendsto_zero_of_summable_integral_pow_four
    (b := fun n => 9 * qvFourthConst * t ^ 4 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun n => Finset.measurable_sum _ fun j _ => measurable_qvIncr B k t n j)
    (fun n => integrable_pow_of_memLp_four (hLp n) le_rfl) ?_ fun n => ?_
  · exact ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  · have h := integral_sum_pow_four_le (iIndepFun_qvIncr B k ht n)
      (fun j => measurable_qvIncr B k t n j) (fun j => memLp_qvIncr B k ht n j)
      (fun j => integral_qvIncr B k ht n j)
      (M := qvFourthConst * (t / ((n : ℝ) + 1)) ^ 4)
      (fun j => (integral_qvIncr_pow_four B k ht n j).le) (s n)
    refine h.trans ?_
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcard : ((s n).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hs n
    have hcard2 : ((s n).card : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    have hM : 0 ≤ qvFourthConst * (t / ((n : ℝ) + 1)) ^ 4 := by positivity
    calc 9 * ((s n).card : ℝ) ^ 2 * (qvFourthConst * (t / ((n : ℝ) + 1)) ^ 4)
        ≤ 9 * ((n : ℝ) + 1) ^ 2 * (qvFourthConst * (t / ((n : ℝ) + 1)) ^ 4) := by
          gcongr
      _ = 9 * qvFourthConst * t ^ 4 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          push_cast
          field_simp

/-- **Pathwise Föllmer hypothesis, almost surely.** Simultaneously for all rational block
boundaries `i / K`, the centred squared increments with `j / (n+1) < i / K` sum to `o(1)`. -/
theorem ae_tendsto_qvBlocks (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ K i : ℕ, Tendsto (fun n =>
      ∑ j ∈ (range (n + 1)).filter (fun j => j * K < i * (n + 1)), qvIncr B k t n j ω)
      atTop (𝓝 0) := by
  rw [ae_all_iff]
  intro K
  rw [ae_all_iff]
  intro i
  refine ae_tendsto_qvBlock B k ht _ fun n => ?_
  exact (Finset.card_filter_le _ _).trans (by simp)

end SignatureVolatility
