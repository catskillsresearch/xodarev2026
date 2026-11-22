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

/-- For `0 < h`, `(σ_v - σ_u)⁸` is dominated by an explicit integrable majorant. -/
lemma signatureSigma_sub_pow_eight_le {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {ℓ : ExtTensorAlgebra (d + 1)} {C r : ℝ}
    (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) {u v h : ℝ} (hh : 0 < h) (ω : Ω) :
    (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 8 ≤
      (C * r) ^ 8 / 2 * (((d : ℝ) + 1) ^ 7 / h ^ 4) *
          ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 +
        (C * r) ^ 8 / 2 * (h ^ 4 / 2) * Real.exp (32 * r * incrNorm B u ω) +
        (C * r) ^ 8 / 2 * (h ^ 4 / 2) * Real.exp (32 * r * incrNorm B v ω) := by
  set N2 : ℝ := ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 2 with hN2
  set S16 : ℝ := ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 with hS16
  set iu := incrNorm B u ω
  set iv := incrNorm B v ω
  set E : ℝ := Real.exp (r * (iu + iv)) with hE
  have hN20 : 0 ≤ N2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hσ := abs_signatureSigma_sub_le B hT hℓ u v ω
  have h8 : (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 8 ≤
      (C * r) ^ 8 * (N2 ^ 4 * E ^ 8) := by
    rw [← (by decide : Even 8).pow_abs]
    calc |signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω| ^ 8
        ≤ (C * r * Real.sqrt N2 * E) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hσ 8
      _ = (C * r) ^ 8 * ((Real.sqrt N2 ^ 2) ^ 4 * E ^ 8) := by ring
      _ = (C * r) ^ 8 * (N2 ^ 4 * E ^ 8) := by rw [Real.sq_sqrt hN20]
  have hamgm : N2 ^ 4 * E ^ 8 ≤ (N2 ^ 8 / h ^ 4 + h ^ 4 * (E ^ 8) ^ 2) / 2 := by
    have hkey : (N2 ^ 4 / h ^ 2 - h ^ 2 * E ^ 8) ^ 2 =
        N2 ^ 8 / h ^ 4 - 2 * (N2 ^ 4 * E ^ 8) + h ^ 4 * (E ^ 8) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (N2 ^ 4 / h ^ 2 - h ^ 2 * E ^ 8)]
  have hN16 : N2 ^ 8 ≤ ((d : ℝ) + 1) ^ 7 * S16 := sum_sq_pow_eight_le _
  have hE16 : (E ^ 8) ^ 2 ≤ (Real.exp (32 * r * iu) + Real.exp (32 * r * iv)) / 2 := by
    have e1 : Real.exp (32 * r * iu) = Real.exp (16 * r * iu) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (32 * r * iv) = Real.exp (16 * r * iv) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : (E ^ 8) ^ 2 = Real.exp (16 * r * iu) * Real.exp (16 * r * iv) := by
      rw [← pow_mul, hE, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, e3]
    nlinarith [sq_nonneg (Real.exp (16 * r * iu) - Real.exp (16 * r * iv))]
  have hCr : 0 ≤ (C * r) ^ 8 := by positivity
  calc (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 8
      ≤ (C * r) ^ 8 * (N2 ^ 4 * E ^ 8) := h8
    _ ≤ (C * r) ^ 8 * ((N2 ^ 8 / h ^ 4 + h ^ 4 * (E ^ 8) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hamgm hCr
    _ ≤ (C * r) ^ 8 * ((((d : ℝ) + 1) ^ 7 * S16 / h ^ 4 +
          h ^ 4 * ((Real.exp (32 * r * iu) + Real.exp (32 * r * iv)) / 2)) / 2) := by
        gcongr
    _ = _ := by ring

/-- **`L⁸`-Hölder-`1/2` regularity of `σ = ⟨ℓ, Ŵ⟩` under H1–H2.** -/
theorem holderAdapted8_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (t : ℝ) :
    ∃ K, HolderAdapted8 B (signatureSigma B hT ℓ) t K := by
  obtain ⟨C, r, hC, hr, hℓn⟩ := exists_levelNorm_le_geometric hw hℓ
  set c : ℝ := 32 * r with hc
  have hc0 : 0 ≤ c := by positivity
  set Eb : ℝ := 2 * ((d : ℝ) + 1) *
    Real.exp (c * ((d : ℝ) + 1) * t + (c * ((d : ℝ) + 1)) ^ 2 * t / 2) with hEb
  have hEb0 : 0 ≤ Eb := by positivity
  refine ⟨(C * r) ^ 8 / 2 * (((d : ℝ) + 1) ^ 8 * (t ^ 8 + gauss16Const) + Eb), ?_⟩
  have hmeasA : ∀ u, 0 ≤ u → AEStronglyMeasurable (signatureSigma B hT ℓ u) P := fun u hu =>
    ((measurable_signatureSigma_path B hT ℓ u ⟨u, hu, le_rfl⟩).mono
      ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable
  refine ⟨by have := gauss16Const_nonneg; positivity, fun u hu _ =>
    measurable_signatureSigma_path B hT ℓ u ⟨u, hu, le_rfl⟩, ?_, ?_⟩
  · intro u hu _
    have hint : Integrable (fun ω => Real.exp ((8 * r) * incrNorm B u ω)) P :=
      integrable_exp_mul_incrNorm B u (by positivity)
    have hg : MemLp (fun ω => Real.exp (r * incrNorm B u ω)) 8 P := by
      have hmeas : AEStronglyMeasurable (fun ω => Real.exp (r * incrNorm B u ω)) P :=
        ((measurable_incrNorm B u).const_mul r).exp.aestronglyMeasurable
      have h8 : MemLp (fun ω => Real.exp (r * incrNorm B u ω)) ((8 : ℕ) : ℝ≥0∞) P := by
        rw [← integrable_norm_rpow_iff hmeas (by simp) (by simp)]
        simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, Real.abs_exp]
        refine hint.congr (ae_of_all _ fun ω => ?_)
        simp only
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      exact_mod_cast h8
    refine (hg.const_mul C).mono' (hmeasA u hu) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_signatureSigma_le B hT hℓn u ω
  · intro u v hu huv hvt
    rcases huv.eq_or_lt with rfl | hlt
    · simp
    have hut : u ≤ t := huv.trans hvt
    set h : ℝ := v - u with hh
    have hh0 : 0 < h := sub_pos.mpr hlt
    set A : ℝ := (C * r) ^ 8 / 2 * (((d : ℝ) + 1) ^ 7 / h ^ 4) with hA
    set Bc : ℝ := (C * r) ^ 8 / 2 * (h ^ 4 / 2) with hBc
    have hA0 : 0 ≤ A := by positivity
    have hBc0 : 0 ≤ Bc := by positivity
    have hS16 : Integrable (fun ω => ∑ j,
        (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16) P :=
      integrable_finsetSum _ fun j _ => integrable_wAug_sub_pow16 B hu huv j
    have hEu : Integrable (fun ω => Real.exp (32 * r * incrNorm B u ω)) P :=
      integrable_exp_mul_incrNorm B u (by positivity)
    have hEv : Integrable (fun ω => Real.exp (32 * r * incrNorm B v ω)) P :=
      integrable_exp_mul_incrNorm B v (by positivity)
    have hIu : ∫ ω, Real.exp (32 * r * incrNorm B u ω) ∂P ≤ Eb :=
      integral_exp_mul_incrNorm_le B hc0 hu hut
    have hIv : ∫ ω, Real.exp (32 * r * incrNorm B v ω) ∂P ≤ Eb :=
      integral_exp_mul_incrNorm_le B hc0 (hu.trans huv) hvt
    have hI16 : ∑ j, ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 ∂P ≤
        ∑ _j : Fin (d + 1), (t ^ 8 + gauss16Const) * h ^ 8 :=
      Finset.sum_le_sum fun j _ => integral_wAug_sub_pow16_le B hu huv hvt j
    calc ∫ ω, (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 8 ∂P
        ≤ ∫ ω, (A * ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 +
            Bc * Real.exp (32 * r * incrNorm B u ω) +
            Bc * Real.exp (32 * r * incrNorm B v ω)) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
            (((hS16.const_mul A).add (hEu.const_mul Bc)).add (hEv.const_mul Bc))
            (ae_of_all _ fun ω => signatureSigma_sub_pow_eight_le B hT hℓn hh0 ω)
      _ = A * ∑ j, ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 ∂P +
            Bc * ∫ ω, Real.exp (32 * r * incrNorm B u ω) ∂P +
            Bc * ∫ ω, Real.exp (32 * r * incrNorm B v ω) ∂P := by
          have hfirst : Integrable (fun ω => A * ∑ j,
              (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 16 +
              Bc * Real.exp (32 * r * incrNorm B u ω)) P :=
            (hS16.const_mul A).add (hEu.const_mul Bc)
          rw [integral_add hfirst (hEv.const_mul Bc),
            integral_add (hS16.const_mul A) (hEu.const_mul Bc), integral_const_mul,
            integral_const_mul, integral_const_mul,
            integral_finsetSum _ fun j _ => integrable_wAug_sub_pow16 B hu huv j]
      _ ≤ A * ∑ _j : Fin (d + 1), (t ^ 8 + gauss16Const) * h ^ 8 + Bc * Eb + Bc * Eb := by
          gcongr
      _ = (C * r) ^ 8 / 2 * (((d : ℝ) + 1) ^ 8 * (t ^ 8 + gauss16Const) + Eb) * h ^ 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hA, hBc]
          push_cast
          field_simp
          ring

end SignatureVolatility
