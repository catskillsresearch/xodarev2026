module

public import SignatureVolatility.ItoCalculusKit.EvenMoment
public import SignatureVolatility.ItoCalculusKit.RiemannConvergence


@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal


namespace SignatureVolatility

/-!
# Even-moment bound for adapted Itô–Riemann sums

`nrm_transform_le`: for `q ≥ 2`, a partition `τ` and `𝓕_{τ j}`-measurable `h j ∈ L^{2q}`,

`‖∑_{j<m} h_j ΔW_j‖_{2q}² ≤ evenConst q · (𝔼G^{2q})^{1/q} · ∑_{j<m} ‖h_j‖_{2q}² (τ(j+1) - τ j)`.

Also the Gaussian sixteenth moment used by the `L⁸`-Hölder bound of the volatility.
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


/-- `𝔼[G^{2q}]` for a standard Gaussian. -/
noncomputable def gaussMoment (q : ℕ) : ℝ := ∫ y, y ^ (2 * q) ∂(gaussianReal 0 1)

lemma gaussMoment_nonneg (q : ℕ) : 0 ≤ gaussMoment q :=
  integral_nonneg fun y => Even.pow_nonneg ⟨q, by ring⟩ _

lemma integrable_pow_even_gaussianReal (q : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ (2 * q)) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((2 * q : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)).integrable_norm_pow'
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [id_eq, Real.norm_eq_abs]
  exact (Even.pow_abs ⟨q, by ring⟩ x)

lemma integral_pow_even_gaussianReal (q : ℕ) (v : ℝ≥0) :
    ∫ x, x ^ (2 * q) ∂(gaussianReal 0 v) = gaussMoment q * (v : ℝ) ^ q := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ y : ℝ, (Real.sqrt v * y) ^ (2 * q) = (v : ℝ) ^ q * y ^ (2 * q) := by
    intro y
    rw [mul_pow, pow_mul, Real.sq_sqrt v.coe_nonneg]
  simp_rw [hpt]
  rw [integral_const_mul, gaussMoment, mul_comm]

lemma integrable_wnnIncr_pow_even (B : MultiBrownian Ω P d) (k : Fin d) (q : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : Integrable (fun ω => wnnIncr B k a b ω ^ (2 * q)) P :=
  (hasLaw_wnnIncr B k ha hab).integrable_comp (integrable_pow_even_gaussianReal q _)

lemma integral_wnnIncr_pow_even (B : MultiBrownian Ω P d) (k : Fin d) (q : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, wnnIncr B k a b ω ^ (2 * q) ∂P = gaussMoment q * (b - a) ^ q := by
  have hcomp := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x ^ (2 * q))
    (measurable_id.pow_const _).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow_even_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.mpr hab)]

omit [IsProbabilityMeasure P] in
lemma memLp_even_of_integrable_pow {q : ℕ} {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h : Integrable (fun ω => f ω ^ (2 * q)) P) : MemLp f (2 * q : ℕ) P := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simpa using hf
  rw [← integrable_norm_rpow_iff hf (by simp; omega) (ENNReal.natCast_ne_top _)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact (Even.pow_abs ⟨q, by ring⟩ _).symm

/-- An `𝓕_s`-measurable `L^{2q}` variable times the driver increment over `[s, u]`. -/
lemma memLp_mul_wnnIncr_even (B : MultiBrownian Ω P d) (k : Fin d) (q : ℕ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s ≤ u) {h : Ω → ℝ} (hmeas : Measurable[(pathFiltration B).σAlg s] h)
    (hLp : MemLp h (2 * q : ℕ) P) : MemLp (fun ω => h ω * wnnIncr B k s u ω) (2 * q : ℕ) P := by
  have hhm : Measurable h := hmeas.mono ((pathFiltration B).le_ambient _) le_rfl
  have hi := ((indepFun_pathFiltration_wnnIncr B k hsu hmeas).comp
    (measurable_id.pow_const (2 * q)) (measurable_id.pow_const (2 * q))).integrable_mul
    (integrable_pow_of_memLp_evenDeg ⟨q, by ring⟩ hLp) (integrable_wnnIncr_pow_even B k q hs hsu)
  refine memLp_even_of_integrable_pow
    (hhm.mul (measurable_wnnIncr B k s u)).aestronglyMeasurable
    (hi.congr (ae_of_all _ fun ω => ?_))
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]
  ring

/-- **Discrete Itô `L^{2q}` bound in the joint filtration** (squared-norm form). -/
theorem nrm_transform_le (B : MultiBrownian Ω P d) (k : Fin d) {q : ℕ} (hq : 2 ≤ q)
    {τ : ℕ → ℝ} (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (h : ℕ → Ω → ℝ) (m : ℕ)
    (hmeas : ∀ j < m, Measurable[(pathFiltration B).σAlg (τ j)] (h j))
    (hLp : ∀ j < m, MemLp (h j) (2 * q : ℕ) P) :
    nrm q (∫ ω, (∑ j ∈ range m, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ (2 * q) ∂P) ≤
      evenConst q * nrm q (gaussMoment q) *
        ∑ j ∈ range m, nrm q (∫ ω, h j ω ^ (2 * q) ∂P) * (τ (j + 1) - τ j) := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hq0 : q ≠ 0 := by omega
  have hτn : ∀ j, 0 ≤ τ j := fun j => hτ0.trans (hτ (Nat.zero_le j))
  have hstep : ∀ j, τ j ≤ τ (j + 1) := fun j => hτ (Nat.le_succ j)
  set w : ℕ → Ω → ℝ := fun j ω => wnnIncr B k (τ j) (τ (j + 1)) ω with hw
  set ξ : ℕ → Ω → ℝ := fun j ω => h j ω * w j ω with hξ
  have hwmeas : ∀ j, Measurable (w j) := fun j => measurable_wnnIncr B k _ _
  have hwlaw : ∀ j, HasLaw (w j) (gaussianReal 0 (Real.toNNReal (τ (j + 1) - τ j))) P :=
    fun j => hasLaw_wnnIncr B k (hτn j) (hstep j)
  have hwq : ∀ j, ∫ ω, w j ω ^ (2 * q) ∂P = gaussMoment q * (τ (j + 1) - τ j) ^ q := fun j =>
    integral_wnnIncr_pow_even B k q (hτn j) (hstep j)
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
  have hξLp : ∀ j < m, MemLp (ξ j) (2 * q : ℕ) P := fun j hj =>
    memLp_mul_wnnIncr_even B k q (hτn j) (hstep j) (hmeas j hj) (hLp j hj)
  have hξq : ∀ j < m, ∫ ω, ξ j ω ^ (2 * q) ∂P =
      (∫ ω, h j ω ^ (2 * q) ∂P) * (gaussMoment q * (τ (j + 1) - τ j) ^ q) := by
    intro j hj
    have h1 := (hind j (h j) (hmeas j hj)).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x ^ (2 * q)) (g := fun y : ℝ => y ^ (2 * q))
      (hhm j hj).aemeasurable (hwmeas j).aemeasurable
      (measurable_id.pow_const _).aestronglyMeasurable
      (measurable_id.pow_const _).aestronglyMeasurable
    rw [hwq j] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ (2 * q - 1) * ξ j ω ∂P = 0 := by
    intro j hj
    have hMm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := Finset.mem_range.mp hi
      exact ((hmeas i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul
        (measurable_wnnIncr_pathFiltration B k (hτn i) (hτn (i + 1)) (hτ hij.le)
          (hτ (Nat.succ_le_of_lt hij)))
    have hg : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ (2 * q - 1) * h j ω) :=
      (hMm.pow_const _).mul (hmeas j hj)
    have h1 := (hind j _ hg).integral_fun_mul_eq_mul_integral
      (hg.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (hwmeas j).aestronglyMeasurable
    rw [hw1 j, mul_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  refine (nrm_sum_le_of_orthogonal hq m hξLp horth).trans (le_of_eq ?_)
  have hC := gaussMoment_nonneg q
  have hsum : ∑ j ∈ range m, nrm q (∫ ω, ξ j ω ^ (2 * q) ∂P) =
      nrm q (gaussMoment q) *
        ∑ j ∈ range m, nrm q (∫ ω, h j ω ^ (2 * q) ∂P) * (τ (j + 1) - τ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hδ : 0 ≤ τ (j + 1) - τ j := sub_nonneg.mpr (hstep j)
    rw [hξq j (Finset.mem_range.mp hj), nrm_mul q (integral_nonneg fun ω => hev.pow_nonneg _)
      (by positivity), nrm_mul q hC (by positivity), nrm_pow_self hq0 hδ]
    ring
  rw [hsum]; ring

end SignatureVolatility
