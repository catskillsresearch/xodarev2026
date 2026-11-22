module

public import SignatureVolatility.ItoCalculusKit.EighthMoment
public import SignatureVolatility.ItoCalculusKit.SigmaHolder


@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace SignatureVolatility

/-!
# Eighth-moment bound for adapted Itô–Riemann sums

`integral_transform_pow_eight_le`: for a partition `τ` and `𝓕_{τ j}`-measurable `h j ∈ L⁸`,

`𝔼[(∑_{j<m} h_j ΔW_j)⁸] ≤ (14 · c₈^{1/4} · ∑_{j<m} (𝔼 h_j⁸)^{1/4} (τ(j+1) - τ j))⁴`,

with `c₈ = 𝔼[G⁸]` (`gauss8Const`). The eighth-order analogue of
`integral_transform_pow_four_le`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma root4_mul {x y : ℝ} (hx : 0 ≤ x) : root4 (x * y) = root4 x * root4 y := by
  unfold root4
  rw [Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg _)]

lemma root4_pow_four_self {x : ℝ} (hx : 0 ≤ x) : root4 (x ^ 4) = x := by
  unfold root4
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq hx]

omit [IsProbabilityMeasure P] in
lemma memLp_eight_of_integrable_pow_eight {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h : Integrable (fun ω => f ω ^ 8) P) : MemLp f 8 P := by
  have h8 : MemLp f ((8 : ℕ) : ℝ≥0∞) P := by
    rw [← integrable_norm_rpow_iff hf (by simp) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  exact_mod_cast h8

/-- An `𝓕_s`-measurable `L⁸` variable times the driver increment over `[s, u]` is in `L⁸`. -/
lemma memLp_mul_wnnIncr_eight (B : MultiBrownian Ω P d) (k : Fin d) {s u : ℝ} (hs : 0 ≤ s)
    (hsu : s ≤ u) {h : Ω → ℝ} (hmeas : Measurable[(pathFiltration B).σAlg s] h)
    (hLp : MemLp h 8 P) : MemLp (fun ω => h ω * wnnIncr B k s u ω) 8 P := by
  have hhm : Measurable h := hmeas.mono ((pathFiltration B).le_ambient _) le_rfl
  have hi := ((indepFun_pathFiltration_wnnIncr B k hsu hmeas).comp (measurable_id.pow_const 8)
    (measurable_id.pow_const 8)).integrable_mul
    (integrable_pow_of_memLp_eight hLp le_rfl) (integrable_wnnIncr_pow8 B k hs hsu)
  refine memLp_eight_of_integrable_pow_eight
    (hhm.mul (measurable_wnnIncr B k s u)).aestronglyMeasurable
    (hi.congr (ae_of_all _ fun ω => ?_))
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]
  ring

/-- **Discrete Itô `L⁸` bound in the joint filtration.** -/
theorem integral_transform_pow_eight_le (B : MultiBrownian Ω P d) (k : Fin d) {τ : ℕ → ℝ}
    (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (h : ℕ → Ω → ℝ) (m : ℕ)
    (hmeas : ∀ j < m, Measurable[(pathFiltration B).σAlg (τ j)] (h j))
    (hLp : ∀ j < m, MemLp (h j) 8 P) :
    ∫ ω, (∑ j ∈ range m, h j ω * wnnIncr B k (τ j) (τ (j + 1)) ω) ^ 8 ∂P ≤
      (14 * root4 gauss8Const *
        ∑ j ∈ range m, root4 (∫ ω, h j ω ^ 8 ∂P) * (τ (j + 1) - τ j)) ^ 4 := by
  have hτn : ∀ j, 0 ≤ τ j := fun j => hτ0.trans (hτ (Nat.zero_le j))
  have hstep : ∀ j, τ j ≤ τ (j + 1) := fun j => hτ (Nat.le_succ j)
  set w : ℕ → Ω → ℝ := fun j ω => wnnIncr B k (τ j) (τ (j + 1)) ω with hw
  set ξ : ℕ → Ω → ℝ := fun j ω => h j ω * w j ω with hξ
  have hwmeas : ∀ j, Measurable (w j) := fun j => measurable_wnnIncr B k _ _
  have hwlaw : ∀ j, HasLaw (w j) (gaussianReal 0 (Real.toNNReal (τ (j + 1) - τ j))) P :=
    fun j => hasLaw_wnnIncr B k (hτn j) (hstep j)
  have hw8 : ∀ j, ∫ ω, w j ω ^ 8 ∂P = gauss8Const * (τ (j + 1) - τ j) ^ 4 := fun j =>
    integral_wnnIncr_pow8 B k (hτn j) (hstep j)
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
  have hξLp : ∀ j < m, MemLp (ξ j) 8 P := fun j hj =>
    memLp_mul_wnnIncr_eight B k (hτn j) (hstep j) (hmeas j hj) (hLp j hj)
  have hξ8 : ∀ j < m, ∫ ω, ξ j ω ^ 8 ∂P =
      (∫ ω, h j ω ^ 8 ∂P) * (gauss8Const * (τ (j + 1) - τ j) ^ 4) := by
    intro j hj
    have h1 := (hind j (h j) (hmeas j hj)).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x ^ 8) (g := fun y : ℝ => y ^ 8)
      (hhm j hj).aemeasurable (hwmeas j).aemeasurable
      (measurable_id.pow_const 8).aestronglyMeasurable
      (measurable_id.pow_const 8).aestronglyMeasurable
    rw [hw8 j] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ 7 * ξ j ω ∂P = 0 := by
    intro j hj
    have hMm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := Finset.mem_range.mp hi
      exact ((hmeas i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul
        (measurable_wnnIncr_pathFiltration B k (hτn i) (hτn (i + 1)) (hτ hij.le)
          (hτ (Nat.succ_le_of_lt hij)))
    have hg : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ 7 * h j ω) := (hMm.pow_const 7).mul (hmeas j hj)
    have h1 := (hind j _ hg).integral_fun_mul_eq_mul_integral
      (hg.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (hwmeas j).aestronglyMeasurable
    rw [hw1 j, mul_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ]
    ring
  refine (integral_sum_pow_eight_le_of_orthogonal m hξLp horth).trans (le_of_eq ?_)
  have hC := gauss8Const_nonneg
  have hsum : ∑ j ∈ range m, root4 (∫ ω, ξ j ω ^ 8 ∂P) =
      root4 gauss8Const * ∑ j ∈ range m, root4 (∫ ω, h j ω ^ 8 ∂P) * (τ (j + 1) - τ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hδ : 0 ≤ τ (j + 1) - τ j := sub_nonneg.mpr (hstep j)
    rw [hξ8 j (Finset.mem_range.mp hj), root4_mul (integral_nonneg fun ω => by positivity),
      root4_mul hC, root4_pow_four_self hδ]
    ring
  rw [hsum]; ring

end SignatureVolatility
