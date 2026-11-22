module

public import SignatureVolatility.ItoCalculusKit.FrozenOrthogonal

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SignatureVolatility

/-!
# Adapted transforms of centred squared Brownian increments

`ζ_{a,b} = (W_b - W_a)² - (b - a)` is centred, independent of `𝓕_a`, with
`E ζ⁴ = qvFourthConst (b - a)⁴`; hence `E (∑ hᵢ ζ_{τᵢ,τᵢ₊₁})⁴ ≤ 16 (√q₄ ∑ √(E hᵢ⁴) Δτᵢ²)²`
(`integral_sum_mul_qvIncrR_pow_four_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Centred squared Brownian increment on `[a, b]`. -/
noncomputable def qvIncrR (B : MultiBrownian Ω P d) (k : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
  wnnIncr B k a b ω ^ 2 - (b - a)

section QV

variable (B : MultiBrownian Ω P d) (k : Fin d)

lemma integral_qvIncrR {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ∫ ω, qvIncrR B k a b ω ∂P = 0 := by
  have hv : ((Real.toNNReal (b - a) : NNReal) : ℝ) = b - a := Real.coe_toNNReal _ (sub_nonneg.mpr hab)
  have h0 := integral_sq_sub_gaussianReal (Real.toNNReal (b - a))
  rw [hv] at h0
  have hcomp := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x ^ 2 - (b - a))
    (by fun_prop : Measurable fun x : ℝ => x ^ 2 - (b - a)).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  simp only [qvIncrR]
  rw [hcomp]; exact h0

lemma integrable_qvIncrR_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Integrable (fun ω => qvIncrR B k a b ω ^ 4) P := by
  have hv : ((Real.toNNReal (b - a) : NNReal) : ℝ) = b - a := Real.coe_toNNReal _ (sub_nonneg.mpr hab)
  have hL := memLp_sq_sub_gaussianReal (Real.toNNReal (b - a))
  rw [hv] at hL
  have hi := integrable_pow_of_memLp_four hL (k := 4) le_rfl
  exact (hasLaw_wnnIncr B k ha hab).integrable_comp hi

lemma integral_qvIncrR_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, qvIncrR B k a b ω ^ 4 ∂P = qvFourthConst * (b - a) ^ 4 := by
  have hv : ((Real.toNNReal (b - a) : NNReal) : ℝ) = b - a := Real.coe_toNNReal _ (sub_nonneg.mpr hab)
  have h0 := integral_sq_sub_pow_four_gaussianReal (Real.toNNReal (b - a))
  rw [hv] at h0
  have hcomp := (hasLaw_wnnIncr B k ha hab).integral_comp
    (f := fun x : ℝ => (x ^ 2 - (b - a)) ^ 4)
    (by fun_prop : Measurable fun x : ℝ => (x ^ 2 - (b - a)) ^ 4).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  simp only [qvIncrR]
  rw [hcomp]; exact h0

lemma qvFourthConst_nonneg : 0 ≤ qvFourthConst :=
  integral_nonneg fun y => by positivity

/-- **`L⁴` bound for adapted transforms of centred squared increments.** -/
theorem integral_sum_mul_qvIncrR_pow_four_le {τ : ℕ → ℝ} (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ)
    (m : ℕ) {h : ℕ → Ω → ℝ} (hmeas : ∀ i < m, Measurable[(pathFiltration B).σAlg (τ i)] (h i))
    (hLp : ∀ i < m, MemLp (h i) 4 P) :
    ∫ ω, (∑ i ∈ range m, h i ω * qvIncrR B k (τ i) (τ (i + 1)) ω) ^ 4 ∂P ≤
      16 * (Real.sqrt qvFourthConst *
        ∑ i ∈ range m, Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i) ^ 2) ^ 2 := by
  have hτn : ∀ i, 0 ≤ τ i := fun i => hτ0.trans (hτ (Nat.zero_le i))
  have hstep : ∀ i, τ i ≤ τ (i + 1) := fun i => hτ (Nat.le_succ i)
  set ζ : ℕ → Ω → ℝ := fun i => qvIncrR B k (τ i) (τ (i + 1)) with hζ
  set φ : ℕ → ℝ → ℝ := fun i x => x ^ 2 - (τ (i + 1) - τ i) with hφ
  have hφm : ∀ i, Measurable (φ i) := fun i => by fun_prop
  have hζeq : ∀ i, ζ i = fun ω => φ i (wnnIncr B k (τ i) (τ (i + 1)) ω) := fun i => rfl
  have hζm : ∀ i, Measurable (ζ i) := fun i => by
    rw [hζeq]; exact (hφm i).comp (measurable_wnnIncr B k _ _)
  have hind : ∀ i, ∀ g : Ω → ℝ, Measurable[(pathFiltration B).σAlg (τ i)] g →
      IndepFun g (ζ i) P := fun i g hg => by
    rw [hζeq]
    exact (indepFun_pathFiltration_wnnIncr B k (hstep i) hg).comp measurable_id (hφm i)
  have hhm : ∀ i < m, Measurable (h i) := fun i hi =>
    (hmeas i hi).mono ((pathFiltration B).le_ambient _) le_rfl
  set ξ : ℕ → Ω → ℝ := fun i ω => h i ω * ζ i ω with hξ
  have hξ4eq : ∀ i < m, ∫ ω, ξ i ω ^ 4 ∂P =
      (∫ ω, h i ω ^ 4 ∂P) * (qvFourthConst * (τ (i + 1) - τ i) ^ 4) := by
    intro i hi
    have h1 := (hind i (h i) (hmeas i hi)).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x ^ 4) (g := fun y : ℝ => y ^ 4)
      (hhm i hi).aemeasurable (hζm i).aemeasurable
      (measurable_id.pow_const 4).aestronglyMeasurable
      (measurable_id.pow_const 4).aestronglyMeasurable
    rw [integral_qvIncrR_pow_four B k (hτn i) (hstep i)] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]; ring
  have hLξ : ∀ i < m, MemLp (ξ i) 4 P := by
    intro i hi
    have hi4 := ((hind i (h i) (hmeas i hi)).comp (measurable_id.pow_const 4)
      (measurable_id.pow_const 4)).integrable_mul
      (integrable_pow_of_memLp_four (hLp i hi) le_rfl)
      (integrable_qvIncrR_pow_four B k (hτn i) (hstep i))
    refine memLp_four_of_integrable_pow_four ((hhm i hi).mul (hζm i)).aestronglyMeasurable
      (hi4.congr (ae_of_all _ fun ω => ?_))
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, hξ]
    ring
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ 3 * ξ j ω ^ 1 ∂P = 0 := by
    intro j hj
    have hSm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := mem_range.mp hi
      refine ((hmeas i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul ?_
      rw [hζeq]
      exact (hφm i).comp (measurable_wnnIncr_pathFiltration B k (hτn i) (hτn (i + 1))
        (hτ hij.le) (hτ (Nat.succ_le_of_lt hij)))
    have hg : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ 3 * h j ω) := (hSm.pow_const 3).mul (hmeas j hj)
    have h1 := (hind j _ hg).integral_fun_mul_eq_mul_integral
      (hg.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (hζm j).aestronglyMeasurable
    rw [show ∫ ω, ζ j ω ∂P = 0 from integral_qvIncrR B k (hτn j) (hstep j), mul_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]; ring
  refine (integral_sum_pow_four_le_of_orthogonal m hLξ horth).trans (le_of_eq ?_)
  have hq := qvFourthConst_nonneg
  have hsum : ∑ i ∈ range m, Real.sqrt (∫ ω, ξ i ω ^ 4 ∂P) = Real.sqrt qvFourthConst *
      ∑ i ∈ range m, Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hδ : 0 ≤ τ (i + 1) - τ i := sub_nonneg.mpr (hstep i)
    rw [hξ4eq i (mem_range.mp hi), Real.sqrt_mul (integral_nonneg fun ω => by positivity),
      Real.sqrt_mul hq, show (τ (i + 1) - τ i) ^ 4 = ((τ (i + 1) - τ i) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  rw [hsum]

end QV

end SignatureVolatility
