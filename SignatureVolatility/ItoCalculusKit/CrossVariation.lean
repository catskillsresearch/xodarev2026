module

public import SignatureVolatility.ItoCalculusKit.FrozenIncrement4
public import SignatureVolatility.ItoCalculusKit.EvenTransform

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SignatureVolatility

/-!
# Discrete cross-variation of two Brownian coordinates

For a cell `[a, b]` the centred product `M = ΔW^{k'} ΔW^k - δ_{k'k} (b - a)` has mean zero, second
moment `≤ (c₂ + 1)(b - a)²` (`c₂ = E Z⁴`), and is independent of the joint past `𝓕_a`.
Consequently, for adapted `L²` weights `g_i`,
`E (Σ_i g_i M_i)² = Σ_i E g_i² · E M_i²` (`integral_sum_mul_cellProd_sq`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Centred product of the increments of coordinates `k'` and `k` over `[a, b]`. -/
def cellProd (B : MultiBrownian Ω P d) (k' k : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
  wnnIncr B k' a b ω * wnnIncr B k a b ω - (if k' = k then b - a else 0)

lemma measurable_cellProd (B : MultiBrownian Ω P d) (k' k : Fin d) (a b : ℝ) :
    Measurable (cellProd B k' k a b) :=
  ((measurable_wnnIncr B k' a b).mul (measurable_wnnIncr B k a b)).sub measurable_const

lemma measurable_cellProd_pathFiltration (B : MultiBrownian Ω P d) (k' k : Fin d) {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (cellProd B k' k a b) :=
  ((measurable_wnnIncr_pathFiltration B k' ha (ha.trans hab) (hab.trans hbT) hbT).mul
    (measurable_wnnIncr_pathFiltration B k ha (ha.trans hab) (hab.trans hbT) hbT)).sub
    measurable_const

/-- The cell product is independent of the joint past. -/
lemma indepFun_pathFiltration_cellProd (B : MultiBrownian Ω P d) (k' k : Fin d) {a b : ℝ}
    (hab : a ≤ b) {g : Ω → ℝ} (hg : Measurable[(pathFiltration B).σAlg a] g) :
    IndepFun g (cellProd B k' k a b) P := by
  by_cases hkk : k' = k
  · subst hkk
    have hφ : Measurable fun x : ℝ => x * x - (b - a) :=
      (measurable_id.mul measurable_id).sub_const _
    have h := (indepFun_pathFiltration_wnnIncr B k' hab hg).comp measurable_id hφ
    have e : cellProd B k' k' a b =
        (fun x : ℝ => x * x - (b - a)) ∘ fun ω => wnnIncr B k' a b ω := by
      funext ω; simp [cellProd]
    rw [e]; exact h
  · have hφ : Measurable fun p : ℝ × ℝ => p.1 * p.2 := measurable_fst.mul measurable_snd
    have h := (indepFun_pathFiltration_wnnIncr_pair B hkk hab hg).comp measurable_id hφ
    have e : cellProd B k' k a b = (fun p : ℝ × ℝ => p.1 * p.2) ∘
        fun ω => (wnnIncr B k' a b ω, wnnIncr B k a b ω) := by
      funext ω; simp [cellProd, hkk]
    rw [e]; exact h

lemma integral_wnnIncr (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ∫ ω, wnnIncr B k a b ω ∂P = 0 := by
  have h := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x)
    measurable_id.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_id_gaussianReal]

lemma integral_sq_gaussianReal_zero (v : NNReal) : ∫ y, y ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := fun x : ℝ => x)
    aemeasurable_id' integral_id_gaussianReal
  rw [variance_fun_id_gaussianReal] at h
  exact h.symm

lemma integral_wnnIncr_sq (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ∫ ω, wnnIncr B k a b ω ^ 2 ∂P = b - a := by
  have h := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x ^ 2)
    (measurable_id.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_sq_gaussianReal_zero, Real.coe_toNNReal _ (sub_nonneg.mpr hab)]

lemma integral_cellProd (B : MultiBrownian Ω P d) (k' k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ∫ ω, cellProd B k' k a b ω ∂P = 0 := by
  have hi : ∀ i, Integrable (fun ω => wnnIncr B i a b ω ^ 2) P := fun i => by
    simpa using integrable_wnnIncr_pow_even B i 1 ha hab
  by_cases hkk : k' = k
  · subst hkk
    simp only [cellProd, ite_true]
    rw [integral_sub (by simpa [sq] using hi k') (integrable_const _), integral_const]
    have := integral_wnnIncr_sq B k' ha hab
    simp only [sq] at this
    simp [this]
  · simp only [cellProd, hkk, ite_false, sub_zero]
    rw [IndepFun.integral_fun_mul_eq_mul_integral (indepFun_wnnIncr_wnnIncr B hkk a b)
      (measurable_wnnIncr B k' a b).aestronglyMeasurable
      (measurable_wnnIncr B k a b).aestronglyMeasurable, integral_wnnIncr B k' ha hab]
    simp

/-- Second moment of the cell product. -/
lemma integrable_cellProd_sq_and_le (B : MultiBrownian Ω P d) (k' k : Fin d) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Integrable (fun ω => cellProd B k' k a b ω ^ 2) P ∧
      ∫ ω, cellProd B k' k a b ω ^ 2 ∂P ≤ (gaussMoment 2 + 1) * (b - a) ^ 2 := by
  have hi : ∀ i, Integrable (fun ω => wnnIncr B i a b ω ^ 2) P := fun i => by
    simpa using integrable_wnnIncr_pow_even B i 1 ha hab
  have hi4 : ∀ i, Integrable (fun ω => wnnIncr B i a b ω ^ 4) P := fun i => by
    simpa using integrable_wnnIncr_pow_even B i 2 ha hab
  have e4 : ∀ i, ∫ ω, wnnIncr B i a b ω ^ 4 ∂P = gaussMoment 2 * (b - a) ^ 2 := fun i => by
    simpa using integral_wnnIncr_pow_even B i 2 ha hab
  have hg0 := gaussMoment_nonneg 2
  by_cases hkk : k' = k
  · subst hkk
    have e : (fun ω => cellProd B k' k' a b ω ^ 2) = fun ω =>
        wnnIncr B k' a b ω ^ 4 - (2 * (b - a)) * wnnIncr B k' a b ω ^ 2 + (b - a) ^ 2 := by
      funext ω; simp only [cellProd, ite_true]; ring
    rw [e]
    have hI := ((hi4 k').sub ((hi k').const_mul (2 * (b - a)))).add
      (integrable_const ((b - a) ^ 2))
    refine ⟨hI, ?_⟩
    rw [integral_add (f := fun ω => wnnIncr B k' a b ω ^ 4 - 2 * (b - a) * wnnIncr B k' a b ω ^ 2)
      (g := fun _ => (b - a) ^ 2) ((hi4 k').sub ((hi k').const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => wnnIncr B k' a b ω ^ 4)
        (g := fun ω => 2 * (b - a) * wnnIncr B k' a b ω ^ 2) (hi4 k') ((hi k').const_mul _),
      integral_const_mul, e4,
      integral_wnnIncr_sq B k' ha hab, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    nlinarith [sq_nonneg (b - a)]
  · have hind := (indepFun_wnnIncr_wnnIncr B hkk a b).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)
    have e : (fun ω => cellProd B k' k a b ω ^ 2) = fun ω =>
        wnnIncr B k' a b ω ^ 2 * wnnIncr B k a b ω ^ 2 := by
      funext ω; simp only [cellProd, hkk, ite_false, sub_zero]; ring
    rw [e]
    refine ⟨hind.integrable_mul (hi k') (hi k), ?_⟩
    have h : ∫ ω, wnnIncr B k' a b ω ^ 2 * wnnIncr B k a b ω ^ 2 ∂P =
        (∫ ω, wnnIncr B k' a b ω ^ 2 ∂P) * ∫ ω, wnnIncr B k a b ω ^ 2 ∂P :=
      hind.integral_fun_mul_eq_mul_integral
        ((measurable_wnnIncr B k' a b).pow_const 2).aestronglyMeasurable
        ((measurable_wnnIncr B k a b).pow_const 2).aestronglyMeasurable
    rw [h, integral_wnnIncr_sq B k' ha hab, integral_wnnIncr_sq B k ha hab]
    nlinarith [sq_nonneg (b - a)]

omit [IsProbabilityMeasure P] in
lemma memLp_two_of_integrable_sq {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h : Integrable (fun ω => f ω ^ 2) P) : MemLp f 2 P := by
  have := memLp_even_of_integrable_pow (q := 1) hf (by simpa using h)
  simpa using this

/-- **Orthogonality of the cross-variation transform.** -/
theorem integral_sum_mul_cellProd_sq (B : MultiBrownian Ω P d) (k' k : Fin d) {τ : ℕ → ℝ}
    (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (g : ℕ → Ω → ℝ) (m : ℕ)
    (hmeas : ∀ i < m, Measurable[(pathFiltration B).σAlg (τ i)] (g i))
    (hL : ∀ i < m, MemLp (g i) 2 P) :
    Integrable (fun ω => (∑ i ∈ range m, g i ω * cellProd B k' k (τ i) (τ (i + 1)) ω) ^ 2) P ∧
    ∫ ω, (∑ i ∈ range m, g i ω * cellProd B k' k (τ i) (τ (i + 1)) ω) ^ 2 ∂P =
      ∑ i ∈ range m, (∫ ω, g i ω ^ 2 ∂P) *
        ∫ ω, cellProd B k' k (τ i) (τ (i + 1)) ω ^ 2 ∂P := by
  set M : ℕ → Ω → ℝ := fun i => cellProd B k' k (τ i) (τ (i + 1)) with hM
  have hτn : ∀ i, 0 ≤ τ i := fun i => hτ0.trans (hτ (Nat.zero_le i))
  have hτs : ∀ i, τ i ≤ τ (i + 1) := fun i => hτ (Nat.le_succ i)
  have hgm : ∀ i < m, Measurable (g i) := fun i hi =>
    (hmeas i hi).mono ((pathFiltration B).le_ambient _) le_rfl
  have hind : ∀ i < m, IndepFun (g i) (M i) P := fun i hi =>
    indepFun_pathFiltration_cellProd B k' k (hτs i) (hmeas i hi)
  set a : ℕ → Ω → ℝ := fun i ω => g i ω * M i ω with ha
  have haL : ∀ i < m, MemLp (a i) 2 P := by
    intro i hi
    have hsq := (hind i hi).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have hint := hsq.integrable_mul (hL i hi).integrable_sq
      (integrable_cellProd_sq_and_le B k' k (hτn i) (hτs i)).1
    refine memLp_two_of_integrable_sq
      ((hgm i hi).mul (measurable_cellProd B k' k _ _)).aestronglyMeasurable
      (hint.congr (ae_of_all _ fun ω => ?_))
    simp only [Pi.mul_apply, Function.comp_apply, id_eq, ha]; ring
  have hexp : ∀ ω, (∑ i ∈ range m, a i ω) ^ 2 =
      ∑ i ∈ range m, ∑ l ∈ range m, a i ω * a l ω := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  have hprod : ∀ i ∈ range m, ∀ l ∈ range m, Integrable (fun ω => a i ω * a l ω) P :=
    fun i hi l hl => integrable_mul_of_memLp_two (haL i (mem_range.1 hi)) (haL l (mem_range.1 hl))
  have hInt : Integrable (fun ω => (∑ i ∈ range m, a i ω) ^ 2) P := by
    simp only [hexp]
    exact integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun l hl => hprod i hi l hl
  -- off-diagonal terms vanish
  have hoff : ∀ i < m, ∀ l < m, i < l → ∫ ω, a i ω * a l ω ∂P = 0 := by
    intro i hi l hl hil
    have hle : τ (i + 1) ≤ τ l := hτ hil
    have hX : Measurable[(pathFiltration B).σAlg (τ l)] (fun ω => a i ω * g l ω) :=
      (((hmeas i hi).mono ((pathFiltration B).mono (hτ hil.le)) le_rfl).mul
        (measurable_cellProd_pathFiltration B k' k (hτn i) (hτs i) hle)).mul (hmeas l hl)
    have h := (indepFun_pathFiltration_cellProd B k' k (hτs l) hX).integral_fun_mul_eq_mul_integral
      (hX.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (measurable_cellProd B k' k _ _).aestronglyMeasurable
    rw [integral_cellProd B k' k (hτn l) (hτs l), mul_zero] at h
    rw [← h]
    congr 1; funext ω; simp only [ha, hM]; ring
  have hdiag : ∀ i < m, ∫ ω, a i ω * a i ω ∂P =
      (∫ ω, g i ω ^ 2 ∂P) * ∫ ω, M i ω ^ 2 ∂P := by
    intro i hi
    have hsq := (hind i hi).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have h := hsq.integral_fun_mul_eq_mul_integral
      ((hgm i hi).pow_const 2).aestronglyMeasurable
      ((measurable_cellProd B k' k _ _).pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at h
    rw [← h]
    congr 1; funext ω; simp only [ha]; ring
  refine ⟨hInt, ?_⟩
  show ∫ ω, (∑ i ∈ range m, a i ω) ^ 2 ∂P =
    ∑ i ∈ range m, (∫ ω, g i ω ^ 2 ∂P) * ∫ ω, M i ω ^ 2 ∂P
  simp only [hexp]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun l hl => hprod i hi l hl]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun l hl => hprod i hi l hl]
  rw [Finset.sum_eq_single i]
  · exact hdiag i (mem_range.1 hi)
  · intro l hl hli
    rcases lt_or_gt_of_ne hli with h | h
    · rw [show (fun ω => a i ω * a l ω) = fun ω => a l ω * a i ω by funext ω; ring]
      exact hoff l (mem_range.1 hl) i (mem_range.1 hi) h
    · exact hoff i (mem_range.1 hi) l (mem_range.1 hl) h
  · intro h; exact absurd hi h

end SignatureVolatility
