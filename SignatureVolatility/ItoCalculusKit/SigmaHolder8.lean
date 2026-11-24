module

public import SignatureVolatility.ItoCalculusKit.ItoIncrement8


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# `L⁸`-Hölder regularity of the signature volatility

Under H1–H2, `σ_u = ⟨ℓ, Ŵ_u⟩` satisfies `E|σ_v - σ_u|⁸ ≤ K (v - u)⁴` on `[0, t]`, is in `L⁸`
and is adapted: `HolderAdapted8 B σ t K` (`holderAdapted8_signatureSigma`). Same proof as
`holderAdapted_signatureSigma`, with Gaussian sixteenth moments.
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

lemma integrable_wAug_sub_pow16 (B : MultiBrownian Ω P d) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (j : Fin (d + 1)) :
    Integrable (fun ω => (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16) P := by
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
    exact integrable_const _
  · simp_rw [wAug_sub_of_ne_zero B u v _ j h]
    exact integrable_wnnIncr_pow16 B _ hu huv

lemma integral_wAug_sub_pow16_le (B : MultiBrownian Ω P d) {u v t : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) (j : Fin (d + 1)) :
    ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 ∂P ≤
      (t ^ 8 + gauss16Const) * (v - u) ^ 8 := by
  have hh : 0 ≤ v - u := sub_nonneg.mpr huv
  have ht8 : 0 ≤ t ^ 8 := by positivity
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte, integral_const, probReal_univ, one_smul]
    have hvu : (v - u) ^ 8 ≤ t ^ 8 :=
      pow_le_pow_left₀ hh (by linarith) 8
    calc (v - u) ^ 16 = (v - u) ^ 8 * (v - u) ^ 8 := by ring
      _ ≤ t ^ 8 * (v - u) ^ 8 := mul_le_mul_of_nonneg_right hvu (by positivity)
      _ ≤ (t ^ 8 + gauss16Const) * (v - u) ^ 8 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right gauss16Const_nonneg) (by positivity)
  · simp_rw [wAug_sub_of_ne_zero B u v _ j h]
    rw [integral_wnnIncr_pow16 B _ hu huv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht8) (by positivity)

lemma sum_sq_pow_eight_le (Δ : Fin (d + 1) → ℝ) :
    (∑ j, Δ j ^ 2) ^ 8 ≤ ((d : ℝ) + 1) ^ 7 * ∑ j, Δ j ^ 16 := by
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun j => Δ j ^ 2) (fun j _ => sq_nonneg _) 7
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) ^ 7 := by positivity
  rw [div_le_iff₀ hpos] at h
  have h16 : ∀ j, (Δ j ^ 2) ^ (7 + 1) = Δ j ^ 16 := fun j => by ring
  simp only [h16] at h
  push_cast at h
  have h8 : (∑ j, Δ j ^ 2) ^ 8 = (∑ j, Δ j ^ 2) ^ (7 + 1) := rfl
  rw [h8]
  linarith [h]

/-- **`L⁸`-Hölder-`1/2` regularity of `σ = ⟨ℓ, Ŵ⟩` under H1–H2.** -/
theorem holderAdapted8_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (t : ℝ) :
    ∃ K, HolderAdapted8 B (signatureSigma B hT ℓ) t K := by
  sorry

end SignatureVolatility
