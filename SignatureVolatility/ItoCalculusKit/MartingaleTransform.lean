module

public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ItoCalculusKit.JointPast


@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

noncomputable section

namespace SignatureVolatility

/-!
# Fourth-moment bound for adapted Itô–Riemann sums in the joint filtration

For a partition `τ 0 ≤ τ 1 ≤ …` and integrand values `h j ∈ L⁴` that are measurable for the
**joint** path filtration `𝓕_{τ j}` of all coordinates (e.g. `h j = σ_{τ j}` for a signature
volatility), the discrete stochastic integral against one driver coordinate satisfies

`𝔼[(∑_{j<m} h_j (W^k_{τ(j+1)} - W^k_{τ j}))⁴] ≤ 16 · 𝔼[G⁴] · (∑_{j<m} √𝔼[h_j⁴] (τ(j+1) - τ j))²`

(`integral_transform_pow_four_le`). This is the discrete Burkholder-type estimate behind
almost-sure, full-sequence convergence of Itô–Riemann sums for adapted integrands; it combines
`integral_sum_pow_four_le_of_orthogonal` with independence of driver increments from the joint
past (`indepFun_pathFiltration_wnnIncr`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- `𝔼[G⁴]` for a standard Gaussian `G` (equal to `3`; only finiteness is used). -/
def gaussFourthConst : ℝ := ∫ y, y ^ 4 ∂(gaussianReal 0 1)

lemma gaussFourthConst_nonneg : 0 ≤ gaussFourthConst :=
  integral_nonneg fun y => by positivity

lemma integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = gaussFourthConst * (v : ℝ) ^ 2 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ y : ℝ, (Real.sqrt v * y) ^ 4 = (v : ℝ) ^ 2 * y ^ 4 := by
    intro y
    rw [mul_pow, show Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 by ring, Real.sq_sqrt v.coe_nonneg]
  simp_rw [hpt]
  rw [integral_const_mul, gaussFourthConst, mul_comm]

omit [IsProbabilityMeasure P] in
lemma memLp_four_of_integrable_pow_four {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h : Integrable (fun ω => f ω ^ 4) P) : MemLp f 4 P := by
  have h4 : MemLp f ((4 : ℕ) : ℝ≥0∞) P := by
    rw [← integrable_norm_rpow_iff hf (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  exact_mod_cast h4

/-- **Discrete Itô `L⁴` bound in the joint filtration.** -/
theorem integral_transform_pow_four_le (B : MultiBrownian Ω P d) (k : Fin d) {τ : ℕ → ℝ}
    (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (h : ℕ → Ω → ℝ) (m : ℕ)
    (hmeas : ∀ j < m, Measurable[(pathFiltration B).σAlg (τ j)] (h j))
    (hLp : ∀ j < m, MemLp (h j) 4 P) :
    ∫ ω, (∑ j ∈ range m, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ 4 ∂P ≤
      16 * gaussFourthConst *
        (∑ j ∈ range m, Real.sqrt (∫ ω, h j ω ^ 4 ∂P) * (τ (j + 1) - τ j)) ^ 2 := by
  have hτn : ∀ j, 0 ≤ τ j := fun j => hτ0.trans (hτ (Nat.zero_le j))
  have hstep : ∀ j, τ j ≤ τ (j + 1) := fun j => hτ (Nat.le_succ j)
  set w : ℕ → Ω → ℝ := fun j ω => wnnIncr B k (τ j) (τ (j + 1)) ω with hw
  set ξ : ℕ → Ω → ℝ := fun j ω => h j ω * w j ω with hξ
  have hwmeas : ∀ j, Measurable (w j) := fun j => measurable_wnnIncr B k _ _
  have hwlaw : ∀ j, HasLaw (w j) (gaussianReal 0 (Real.toNNReal (τ (j + 1) - τ j))) P :=
    fun j => hasLaw_wnnIncr B k (hτn j) (hstep j)
  have hwLp : ∀ j, MemLp (w j) 4 P := fun j =>
    (hwlaw j).memLp (memLp_id_gaussianReal' (μ := 0) 4 (by simp))
  have hw4 : ∀ j, ∫ ω, w j ω ^ 4 ∂P = gaussFourthConst * (τ (j + 1) - τ j) ^ 2 := by
    intro j
    have h1 := (hwlaw j).integral_comp (f := fun x : ℝ => x ^ 4)
      (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable
    rw [integral_pow_four_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.mpr (hstep j))] at h1
    exact h1
  have hw1 : ∀ j, ∫ ω, w j ω ∂P = 0 := by
    intro j
    have h1 := (hwlaw j).integral_eq
    rw [integral_id_gaussianReal] at h1
    exact h1
  have hhm : ∀ j < m, Measurable (h j) := fun j hj =>
    (hmeas j hj).mono ((pathFiltration B).le_ambient _) le_rfl
  -- independence of the integrand value (and of anything `𝓕_{τ j}`-measurable) from `w j`
  have hind : ∀ j, ∀ g : Ω → ℝ, Measurable[(pathFiltration B).σAlg (τ j)] g →
      IndepFun g (w j) P := fun j g hg =>
    indepFun_pathFiltration_wnnIncr B k (hstep j) hg
  -- fourth moments of the summands
  have hξ4i : ∀ j < m, Integrable (fun ω => ξ j ω ^ 4) P := by
    intro j hj
    have hi := ((hind j (h j) (hmeas j hj)).comp (measurable_id.pow_const 4)
      (measurable_id.pow_const 4)).integrable_mul
      (integrable_pow_of_memLp_four (hLp j hj) le_rfl)
      (integrable_pow_of_memLp_four (hwLp j) le_rfl)
    refine hi.congr (ae_of_all _ fun ω => ?_)
    simp only [hξ, Pi.mul_apply, Function.comp_apply, id_eq]
    ring
  have hξLp : ∀ j < m, MemLp (ξ j) 4 P := fun j hj =>
    memLp_four_of_integrable_pow_four
      ((hhm j hj).mul (hwmeas j)).aestronglyMeasurable (hξ4i j hj)
  have hξ4 : ∀ j < m, ∫ ω, ξ j ω ^ 4 ∂P =
      (∫ ω, h j ω ^ 4 ∂P) * (gaussFourthConst * (τ (j + 1) - τ j) ^ 2) := by
    intro j hj
    have h1 := (hind j (h j) (hmeas j hj)).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x ^ 4) (g := fun y : ℝ => y ^ 4)
      (hhm j hj).aemeasurable (hwmeas j).aemeasurable
      (measurable_id.pow_const 4).aestronglyMeasurable
      (measurable_id.pow_const 4).aestronglyMeasurable
    rw [hw4 j] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  -- orthogonality to the cube of the past partial sum
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ 3 * ξ j ω ^ 1 ∂P = 0 := by
    intro j hj
    have hMm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := Finset.mem_range.mp hi
      exact ((hmeas i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul
        (measurable_wnnIncr_pathFiltration B k (hτn i) (hτn (i + 1)) (hτ hij.le)
          (hτ (Nat.succ_le_of_lt hij)))
    have hg : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ 3 * h j ω) := (hMm.pow_const 3).mul (hmeas j hj)
    have h1 := (hind j _ hg).integral_fun_mul_eq_mul_integral
      (hg.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (hwmeas j).aestronglyMeasurable
    rw [hw1 j, mul_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  refine (integral_sum_pow_four_le_of_orthogonal m hξLp horth).trans ?_
  have hC := gaussFourthConst_nonneg
  have hsum : ∑ j ∈ range m, Real.sqrt (∫ ω, ξ j ω ^ 4 ∂P) =
      Real.sqrt gaussFourthConst *
        ∑ j ∈ range m, Real.sqrt (∫ ω, h j ω ^ 4 ∂P) * (τ (j + 1) - τ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hδ : 0 ≤ τ (j + 1) - τ j := sub_nonneg.mpr (hstep j)
    rw [hξ4 j (Finset.mem_range.mp hj),
      Real.sqrt_mul (integral_nonneg fun ω => by positivity),
      Real.sqrt_mul hC, Real.sqrt_sq hδ]
    ring
  rw [hsum, mul_pow, Real.sq_sqrt hC]
  exact le_of_eq (by ring)

end SignatureVolatility
