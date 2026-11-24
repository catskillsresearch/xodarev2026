module

public import SignatureVolatility.ItoCalculusKit.SixteenthMoment
public import SignatureVolatility.ItoCalculusKit.EighthTransform


@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal


namespace SignatureVolatility

/-!
# Sixteenth-moment bound for adapted Itô–Riemann sums

`sq16_transform_le`: for a partition `τ` and `𝓕_{τ j}`-measurable `h j ∈ L¹⁶`,

`‖∑_{j<m} h_j ΔW_j‖₁₆² ≤ c₁₆ · (𝔼G¹⁶)^{1/8} · ∑_{j<m} ‖h_j‖₁₆² (τ(j+1) - τ j)`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- `𝔼[G¹⁶]` for a standard Gaussian (only finiteness is used). -/
noncomputable def gauss16Const : ℝ := ∫ y, y ^ 16 ∂(gaussianReal 0 1)

lemma gauss16Const_nonneg : 0 ≤ gauss16Const :=
  integral_nonneg fun y => by positivity

lemma integrable_pow16_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 16) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((16 : ℕ) : ℝ≥0∞) (by simp)).integrable_norm_pow
    (by norm_num)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [id_eq, Real.norm_eq_abs]
  rw [pow_abs, abs_of_nonneg (by positivity)]

lemma integral_pow16_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 16 ∂(gaussianReal 0 v) = gauss16Const * (v : ℝ) ^ 8 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ y : ℝ, (Real.sqrt v * y) ^ 16 = (v : ℝ) ^ 8 * y ^ 16 := by
    intro y
    rw [mul_pow, show Real.sqrt v ^ 16 = (Real.sqrt v ^ 2) ^ 8 by ring,
      Real.sq_sqrt v.coe_nonneg]
  simp_rw [hpt]
  rw [integral_const_mul, gauss16Const, mul_comm]

lemma integrable_wnnIncr_pow16 (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : Integrable (fun ω => wnnIncr B k a b ω ^ 16) P :=
  (hasLaw_wnnIncr B k ha hab).integrable_comp (integrable_pow16_gaussianReal _)

lemma integral_wnnIncr_pow16 (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ∫ ω, wnnIncr B k a b ω ^ 16 ∂P = gauss16Const * (b - a) ^ 8 := by
  have hcomp := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x ^ 16)
    (measurable_id.pow_const 16).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow16_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.mpr hab)]


lemma sq16_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sq16 (x * y) = sq16 x * sq16 y := by
  unfold sq16; exact Real.mul_rpow hx hy

lemma sq16_pow_eight_self {x : ℝ} (hx : 0 ≤ x) : sq16 (x ^ 8) = x := by
  unfold sq16
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

omit [IsProbabilityMeasure P] in
lemma memLp_sixteen_of_integrable_pow_sixteen {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h : Integrable (fun ω => f ω ^ 16) P) : MemLp f 16 P := by
  have h8 : MemLp f ((16 : ℕ) : ℝ≥0∞) P := by
    rw [← integrable_norm_rpow_iff hf (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  exact_mod_cast h8

/-- Powers up to the sixteenth of an `L¹⁶` variable are integrable. -/
lemma integrable_pow_of_memLp_sixteen {f : Ω → ℝ} (hf : MemLp f 16 P) {k : ℕ} (hk : k ≤ 16) :
    Integrable (fun ω => f ω ^ k) P := by
  have h1 : MemLp f (k : ℝ≥0∞) P := hf.mono_exponent (by exact_mod_cast hk)
  have h2 : Integrable (fun ω => ‖f ω‖ ^ k) P := h1.integrable_norm_pow'
  refine (integrable_norm_iff (hf.aestronglyMeasurable.pow k)).mp ?_
  simpa [norm_pow] using h2

/-- An `𝓕_s`-measurable `L¹⁶` variable times the driver increment over `[s, u]` is in `L¹⁶`. -/
lemma memLp_mul_wnnIncr_sixteen (B : MultiBrownian Ω P d) (k : Fin d) {s u : ℝ} (hs : 0 ≤ s)
    (hsu : s ≤ u) {h : Ω → ℝ} (hmeas : Measurable[(pathFiltration B).σAlg s] h)
    (hLp : MemLp h 16 P) : MemLp (fun ω => h ω * wnnIncr B k s u ω) 16 P := by
  have hhm : Measurable h := hmeas.mono ((pathFiltration B).le_ambient _) le_rfl
  have hi := ((indepFun_pathFiltration_wnnIncr B k hsu hmeas).comp (measurable_id.pow_const 16)
    (measurable_id.pow_const 16)).integrable_mul
    (integrable_pow_of_memLp_sixteen hLp le_rfl) (integrable_wnnIncr_pow16 B k hs hsu)
  refine memLp_sixteen_of_integrable_pow_sixteen
    (hhm.mul (measurable_wnnIncr B k s u)).aestronglyMeasurable
    (hi.congr (ae_of_all _ fun ω => ?_))
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]
  ring

/-- **Discrete Itô `L¹⁶` bound in the joint filtration** (squared-norm form). -/
theorem sq16_transform_le (B : MultiBrownian Ω P d) (k : Fin d) {τ : ℕ → ℝ}
    (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (h : ℕ → Ω → ℝ) (m : ℕ)
    (hmeas : ∀ j < m, Measurable[(pathFiltration B).σAlg (τ j)] (h j))
    (hLp : ∀ j < m, MemLp (h j) 16 P) :
    sq16 (∫ ω, (∑ j ∈ range m, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ 16 ∂P) ≤
      983040 * sq16 gauss16Const *
        ∑ j ∈ range m, sq16 (∫ ω, h j ω ^ 16 ∂P) * (τ (j + 1) - τ j) := by
  have hτn : ∀ j, 0 ≤ τ j := fun j => hτ0.trans (hτ (Nat.zero_le j))
  have hstep : ∀ j, τ j ≤ τ (j + 1) := fun j => hτ (Nat.le_succ j)
  set w : ℕ → Ω → ℝ := fun j ω => wnnIncr B k (τ j) (τ (j + 1)) ω with hw
  set ξ : ℕ → Ω → ℝ := fun j ω => h j ω * w j ω with hξ
  have hwmeas : ∀ j, Measurable (w j) := fun j => measurable_wnnIncr B k _ _
  have hwlaw : ∀ j, HasLaw (w j) (gaussianReal 0 (Real.toNNReal (τ (j + 1) - τ j))) P :=
    fun j => hasLaw_wnnIncr B k (hτn j) (hstep j)
  have hw16 : ∀ j, ∫ ω, w j ω ^ 16 ∂P = gauss16Const * (τ (j + 1) - τ j) ^ 8 := fun j =>
    integral_wnnIncr_pow16 B k (hτn j) (hstep j)
  have hw1 : ∀ j, ∫ ω, w j ω ∂P = 0 := by
    intro j
    have h1 := (hwlaw j).integral_eq
    rw [integral_id_gaussianReal] at h1
    exact h1
  have hhm : ∀ j < m, Measurable (h j) := fun j hj =>
    (hmeas j hj).mono ((pathFiltration B).le_ambient _) le_rfl
  have hind : ∀ j, ∀ g : Ω → ℝ, Measurable[(pathFiltration B).σAlg (τ j)] g →
      IndepFun g (w j) P := fun j g hg =>
    indepFun_pathFiltration_wnnIncr B k (hstep j) hg
  have hξLp : ∀ j < m, MemLp (ξ j) 16 P := fun j hj =>
    memLp_mul_wnnIncr_sixteen B k (hτn j) (hstep j) (hmeas j hj) (hLp j hj)
  have hξ16 : ∀ j < m, ∫ ω, ξ j ω ^ 16 ∂P =
      (∫ ω, h j ω ^ 16 ∂P) * (gauss16Const * (τ (j + 1) - τ j) ^ 8) := by
    intro j hj
    have h1 := (hind j (h j) (hmeas j hj)).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x ^ 16) (g := fun y : ℝ => y ^ 16)
      (hhm j hj).aemeasurable (hwmeas j).aemeasurable
      (measurable_id.pow_const 16).aestronglyMeasurable
      (measurable_id.pow_const 16).aestronglyMeasurable
    rw [hw16 j] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ 15 * ξ j ω ∂P = 0 := by
    intro j hj
    have hMm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := Finset.mem_range.mp hi
      exact ((hmeas i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul
        (measurable_wnnIncr_pathFiltration B k (hτn i) (hτn (i + 1)) (hτ hij.le)
          (hτ (Nat.succ_le_of_lt hij)))
    have hg : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ 15 * h j ω) := (hMm.pow_const 15).mul (hmeas j hj)
    have h1 := (hind j _ hg).integral_fun_mul_eq_mul_integral
      (hg.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (hwmeas j).aestronglyMeasurable
    rw [hw1 j, mul_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  refine (sq16_sum_le_of_orthogonal m hξLp horth).trans (le_of_eq ?_)
  have hC := gauss16Const_nonneg
  have hsum : ∑ j ∈ range m, sq16 (∫ ω, ξ j ω ^ 16 ∂P) =
      sq16 gauss16Const * ∑ j ∈ range m, sq16 (∫ ω, h j ω ^ 16 ∂P) * (τ (j + 1) - τ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hδ : 0 ≤ τ (j + 1) - τ j := sub_nonneg.mpr (hstep j)
    rw [hξ16 j (Finset.mem_range.mp hj), sq16_mul (integral_nonneg fun ω => by positivity)
      (by positivity), sq16_mul hC (by positivity), sq16_pow_eight_self hδ]
    ring
  rw [hsum]; ring

end SignatureVolatility
