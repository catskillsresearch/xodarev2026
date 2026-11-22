module

public import SignatureVolatility.ExtTensorAlgebra.TensorExpLipschitz
public import SignatureVolatility.ItoCalculusKit.RiemannConvergence
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# `L⁴`-Hölder regularity of the signature volatility

Under H1–H2, `σ_u = ⟨ℓ, Ŵ_u⟩` (chordal lift over a Brownian driver) satisfies
`E|σ_v - σ_u|⁴ ≤ K (v - u)²` on `[0, t]`, is in `L⁴` and is adapted, i.e.
`HolderAdapted B σ t K` (`holderAdapted_signatureSigma`).

Ingredients: the deterministic Lipschitz bound `abs_dualPairing_tensorExp_sub_le`, Gaussian
eighth moments of the increments, and exponential moments of `‖x_u‖` uniform in `u ∈ [0, t]`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Gaussian eighth moments -/

/-- `𝔼[G⁸]` for a standard Gaussian (equal to `105`; only finiteness is used). -/
noncomputable def gauss8Const : ℝ := ∫ y, y ^ 8 ∂(gaussianReal 0 1)

lemma gauss8Const_nonneg : 0 ≤ gauss8Const :=
  integral_nonneg fun y => by positivity

lemma integrable_pow8_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 8) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((8 : ℕ) : ℝ≥0∞) (by simp)).integrable_norm_pow
    (by norm_num)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [id_eq, Real.norm_eq_abs]
  rw [pow_abs, abs_of_nonneg (by positivity)]

lemma integral_pow8_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 8 ∂(gaussianReal 0 v) = gauss8Const * (v : ℝ) ^ 4 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ y : ℝ, (Real.sqrt v * y) ^ 8 = (v : ℝ) ^ 4 * y ^ 8 := by
    intro y
    rw [mul_pow, show Real.sqrt v ^ 8 = (Real.sqrt v ^ 2) ^ 4 by ring,
      Real.sq_sqrt v.coe_nonneg]
  simp_rw [hpt]
  rw [integral_const_mul, gauss8Const, mul_comm]

lemma integrable_wnnIncr_pow8 (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : Integrable (fun ω => wnnIncr B k a b ω ^ 8) P :=
  (hasLaw_wnnIncr B k ha hab).integrable_comp (integrable_pow8_gaussianReal _)

lemma integral_wnnIncr_pow8 (B : MultiBrownian Ω P d) (k : Fin d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ∫ ω, wnnIncr B k a b ω ^ 8 ∂P = gauss8Const * (b - a) ^ 4 := by
  have hcomp := (hasLaw_wnnIncr B k ha hab).integral_comp (f := fun x : ℝ => x ^ 8)
    (measurable_id.pow_const 8).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow8_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.mpr hab)]

/-! ## Increments of the time-augmented path -/

lemma wAug_sub_of_ne_zero (B : MultiBrownian Ω P d) (u v : ℝ) (ω : Ω) (j : Fin (d + 1))
    (h : (j : ℕ) ≠ 0) :
    MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j =
      wnnIncr B ⟨j.1 - 1, by have := j.isLt; omega⟩ u v ω := by
  simp only [MultiBrownian.wAug, h, ↓reduceDIte, wnnIncr]
  rfl

lemma integrable_wAug_sub_pow8 (B : MultiBrownian Ω P d) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (j : Fin (d + 1)) :
    Integrable (fun ω => (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8) P := by
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
    exact integrable_const _
  · simp_rw [wAug_sub_of_ne_zero B u v _ j h]
    exact integrable_wnnIncr_pow8 B _ hu huv

lemma integral_wAug_sub_pow8_le (B : MultiBrownian Ω P d) {u v t : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) (j : Fin (d + 1)) :
    ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 ∂P ≤
      (t ^ 4 + gauss8Const) * (v - u) ^ 4 := by
  have hh : 0 ≤ v - u := sub_nonneg.mpr huv
  have ht4 : 0 ≤ t ^ 4 := by positivity
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte, integral_const, probReal_univ, one_smul]
    have hvu : (v - u) ^ 4 ≤ t ^ 4 :=
      pow_le_pow_left₀ hh (by linarith) 4
    calc (v - u) ^ 8 = (v - u) ^ 4 * (v - u) ^ 4 := by ring
      _ ≤ t ^ 4 * (v - u) ^ 4 := mul_le_mul_of_nonneg_right hvu (by positivity)
      _ ≤ (t ^ 4 + gauss8Const) * (v - u) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right gauss8Const_nonneg) (by positivity)
  · simp_rw [wAug_sub_of_ne_zero B u v _ j h]
    rw [integral_wnnIncr_pow8 B _ hu huv]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht4) (by positivity)

lemma sum_sq_pow_four_le (Δ : Fin (d + 1) → ℝ) :
    (∑ j, Δ j ^ 2) ^ 4 ≤ ((d : ℝ) + 1) ^ 3 * ∑ j, Δ j ^ 8 := by
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun j => Δ j ^ 2) (fun j _ => sq_nonneg _) 3
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) ^ 3 := by positivity
  rw [div_le_iff₀ hpos] at h
  have h8 : ∀ j, (Δ j ^ 2) ^ (3 + 1) = Δ j ^ 8 := fun j => by ring
  simp only [h8] at h
  push_cast at h
  have h4 : (∑ j, Δ j ^ 2) ^ 4 = (∑ j, Δ j ^ 2) ^ (3 + 1) := rfl
  rw [h4]
  linarith [h]

/-! ## Exponential moments of the increment norm, uniform in time -/

lemma exp_mul_incrNorm_le_sum (B : MultiBrownian Ω P d) (t : ℝ) {c : ℝ} (hc : 0 ≤ c) (ω : Ω) :
    Real.exp (c * incrNorm B t ω) ≤
      ∑ j, (Real.exp ((c * ((d : ℝ) + 1)) *
          (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j)) +
        Real.exp (-(c * ((d : ℝ) + 1)) *
          (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j))) := by
  set K : ℝ := c * ((d : ℝ) + 1) with hK
  set v : Fin (d + 1) → ℝ :=
    fun j => MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j with hv
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|)
    Finset.univ_nonempty
  have hsum : ∑ j, |v j| ≤ ((d : ℝ) + 1) * |v j₀| := by
    calc ∑ j, |v j| ≤ ∑ _j : Fin (d + 1), |v j₀| :=
          Finset.sum_le_sum fun j hj => hj₀ j hj
      _ = ((d : ℝ) + 1) * |v j₀| := by simp
  have hterm : Real.exp (K * |v j₀|) ≤ Real.exp (K * v j₀) + Real.exp (-K * v j₀) := by
    rcases abs_choice (v j₀) with h | h
    · rw [h]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [h, mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  calc Real.exp (c * incrNorm B t ω)
      ≤ Real.exp (c * ∑ j, |v j|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (incrNorm_le_sum_abs B t ω) hc)
    _ ≤ Real.exp (K * |v j₀|) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hK, mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hc
    _ ≤ Real.exp (K * v j₀) + Real.exp (-K * v j₀) := hterm
    _ ≤ ∑ j, (Real.exp (K * v j) + Real.exp (-K * v j)) :=
        Finset.single_le_sum (f := fun j => Real.exp (K * v j) + Real.exp (-K * v j))
          (fun j _ => by positivity) (Finset.mem_univ j₀)

lemma integral_exp_mul_wAug_sub_le (B : MultiBrownian Ω P d) {a u t : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) (j : Fin (d + 1)) :
    ∫ ω, Real.exp (a * (MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j)) ∂P ≤
      Real.exp (|a| * t + a ^ 2 * t / 2) := by
  have ht : 0 ≤ t := hu.trans hut
  have hat : a * u ≤ |a| * t :=
    (le_abs_self a |>.trans le_rfl |> fun h => mul_le_mul_of_nonneg_right h hu).trans
      (mul_le_mul_of_nonneg_left hut (abs_nonneg a))
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte, sub_zero, integral_const, probReal_univ,
      one_smul]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])
  · simp_rw [wAug_sub_of_ne_zero B 0 u _ j h]
    have hm := mgf_gaussianReal (hasLaw_wnnIncr B ⟨j.1 - 1, by have := j.isLt; omega⟩
      le_rfl hu) a
    simp only [mgf] at hm
    rw [hm, sub_zero, Real.coe_toNNReal _ hu]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ |a| * t := mul_nonneg (abs_nonneg a) ht
    nlinarith [sq_nonneg a]

/-- `E exp(c ‖x_u‖) ≤ 2 (d+1) exp(K t + K² t / 2)` with `K = c (d+1)`, for all `u ∈ [0, t]`. -/
lemma integral_exp_mul_incrNorm_le (B : MultiBrownian Ω P d) {c u t : ℝ} (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    ∫ ω, Real.exp (c * incrNorm B u ω) ∂P ≤
      2 * ((d : ℝ) + 1) * Real.exp (c * ((d : ℝ) + 1) * t + (c * ((d : ℝ) + 1)) ^ 2 * t / 2) := by
  set K : ℝ := c * ((d : ℝ) + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hint : ∀ j : Fin (d + 1), Integrable (fun ω =>
      Real.exp (K * (MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j)) +
        Real.exp (-K * (MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j))) P :=
    fun j => (integrable_exp_mul_wAug_sub B u K j).add (integrable_exp_mul_wAug_sub B u (-K) j)
  calc ∫ ω, Real.exp (c * incrNorm B u ω) ∂P
      ≤ ∫ ω, ∑ j, (Real.exp (K * (MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j)) +
          Real.exp (-K * (MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j))) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le)
          (integrable_finsetSum _ fun j _ => hint j)
          (ae_of_all _ fun ω => exp_mul_incrNorm_le_sum B u hc ω)
    _ = ∑ j : Fin (d + 1), ((∫ ω, Real.exp (K * (MultiBrownian.wAug B u ω j -
            MultiBrownian.wAug B 0 ω j)) ∂P) + ∫ ω, Real.exp (-K * (MultiBrownian.wAug B u ω j -
            MultiBrownian.wAug B 0 ω j)) ∂P) := by
        rw [integral_finsetSum _ fun j _ => hint j]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_add (integrable_exp_mul_wAug_sub B u K j)
          (integrable_exp_mul_wAug_sub B u (-K) j)
    _ ≤ ∑ _j : Fin (d + 1), (Real.exp (K * t + K ^ 2 * t / 2) +
          Real.exp (K * t + K ^ 2 * t / 2)) := by
        refine Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
        · have := integral_exp_mul_wAug_sub_le B (a := K) hu hut j
          rwa [abs_of_nonneg hK0] at this
        · have := integral_exp_mul_wAug_sub_le B (a := -K) hu hut j
          rwa [abs_neg, abs_of_nonneg hK0, neg_sq] at this
    _ = 2 * ((d : ℝ) + 1) * Real.exp (K * t + K ^ 2 * t / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The signature volatility -/

/-- The signature volatility `σ_t(ω) = ⟨ℓ, Ŵ_t(ω)⟩` of the Stratonovich setup over `B`. -/
noncomputable abbrev signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) : ℝ → Ω → ℝ :=
  fun t ω => dualPairing ℓ ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat t ω)

/-- `σ_s = ⟨ℓ, Ŵ_s⟩` is adapted to the path filtration. -/
lemma measurable_signatureSigma_path {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (signatureSigma B hT ℓ s.1) := by
  have hc : ∀ I : Word (d + 1), Measurable[(pathFiltration B).σAlg t]
      (fun ω => ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s.1 ω).coeff I) :=
    fun I => (prolongedBrownianSetup_stratonovich_of_brownian B hT).sig_adapted_to_W t s I
  unfold signatureSigma
  simp only [dualPairing, ExtTensorAlgebra.levelInner]
  have hn : ∀ n : ℕ, Measurable[(pathFiltration B).σAlg t] (fun ω =>
      ∑ I ∈ wordsOfLength (d + 1) n, ℓ.coeff I *
        ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s.1 ω).coeff I) :=
    fun n => Finset.measurable_sum _ fun I _ => (hc I).const_mul _
  let : MeasurableSpace Ω := (pathFiltration B).σAlg t
  exact Measurable.tsum hn

/-- `σ_t = ⟨ℓ, exp⊗(x_t)⟩` with `x_t = (t, W_t) - (0, W_0)`. -/
lemma signatureSigma_eq {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) (t : ℝ) (ω : Ω) :
    signatureSigma B hT ℓ t ω = dualPairing ℓ (ExtTensorAlgebra.tensorExp
      (fun j => MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j)) :=
  congrArg (dualPairing ℓ) (sig2OfBrownian_zero_left B t ω)

/-- H1–H2 give a geometric bound `‖ℓ_n‖ ≤ C rⁿ`. -/
lemma exists_levelNorm_le_geometric {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)}
    (hℓ : HypH1 w ℓ) : ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ ∀ n, ℓ.levelNorm n ≤ C * r ^ n := by
  obtain ⟨r, hr⟩ := hw.le_geometric
  have hr0 : 0 ≤ r := by
    have h1 := hr 1
    rw [pow_one] at h1
    exact (w.pos 1).le.trans h1
  have hS := hℓ.mem_l2w
  have hnn : ∀ n, 0 ≤ ℓ.levelNormSq n / (w n) ^ 2 := fun n =>
    div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg ℓ n) (sq_nonneg _)
  set C : ℝ := Real.sqrt (∑' n, ℓ.levelNormSq n / (w n) ^ 2) with hC
  refine ⟨C, r, Real.sqrt_nonneg _, hr0, fun n => ?_⟩
  have h1 : ℓ.levelNormSq n / (w n) ^ 2 ≤ ∑' n, ℓ.levelNormSq n / (w n) ^ 2 :=
    hS.le_tsum n fun j _ => hnn j
  have hwpos := w.pos n
  have h2 : ℓ.levelNormSq n ≤ (∑' n, ℓ.levelNormSq n / (w n) ^ 2) * (w n) ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at h1
  calc ℓ.levelNorm n = Real.sqrt (ℓ.levelNormSq n) := rfl
    _ ≤ Real.sqrt ((∑' n, ℓ.levelNormSq n / (w n) ^ 2) * (w n) ^ 2) := Real.sqrt_le_sqrt h2
    _ = C * w n := by rw [Real.sqrt_mul (tsum_nonneg hnn), Real.sqrt_sq hwpos.le]
    _ ≤ C * r ^ n := mul_le_mul_of_nonneg_left (hr n) (Real.sqrt_nonneg _)

section Bounds

variable {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) {ℓ : ExtTensorAlgebra (d + 1)} {C r : ℝ}

lemma abs_signatureSigma_le (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) (t : ℝ) (ω : Ω) :
    |signatureSigma B hT ℓ t ω| ≤ C * Real.exp (r * incrNorm B t ω) := by
  rw [signatureSigma_eq]
  exact ExtTensorAlgebra.abs_dualPairing_tensorExp_le ℓ hℓ _ le_rfl

lemma abs_signatureSigma_sub_le (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) (u v : ℝ) (ω : Ω) :
    |signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω| ≤
      C * r * Real.sqrt (∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 2) *
        Real.exp (r * (incrNorm B u ω + incrNorm B v ω)) := by
  rw [signatureSigma_eq, signatureSigma_eq]
  have h := ExtTensorAlgebra.abs_dualPairing_tensorExp_sub_le ℓ hℓ
    (fun j => MultiBrownian.wAug B v ω j - MultiBrownian.wAug B 0 ω j)
    (fun j => MultiBrownian.wAug B u ω j - MultiBrownian.wAug B 0 ω j)
    (R := incrNorm B u ω + incrNorm B v ω)
    (le_add_of_nonneg_left (incrNorm_nonneg B u ω))
    (le_add_of_nonneg_right (incrNorm_nonneg B v ω))
  simpa only [sub_sub_sub_cancel_right] using h

end Bounds

/-! ## The pointwise fourth-power majorant -/

/-- For `0 < h`, `(σ_v - σ_u)⁴` is dominated by an explicit integrable majorant built from
eighth powers of the increments and exponentials of the increment norms. -/
lemma signatureSigma_sub_pow_four_le {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {ℓ : ExtTensorAlgebra (d + 1)} {C r : ℝ}
    (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) {u v h : ℝ} (hh : 0 < h) (ω : Ω) :
    (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 4 ≤
      (C * r) ^ 4 / 2 * (((d : ℝ) + 1) ^ 3 / h ^ 2) *
          ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 +
        (C * r) ^ 4 / 2 * (h ^ 2 / 2) * Real.exp (16 * r * incrNorm B u ω) +
        (C * r) ^ 4 / 2 * (h ^ 2 / 2) * Real.exp (16 * r * incrNorm B v ω) := by
  set N2 : ℝ := ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 2 with hN2
  set S8 : ℝ := ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 with hS8
  set iu := incrNorm B u ω
  set iv := incrNorm B v ω
  set E : ℝ := Real.exp (r * (iu + iv)) with hE
  have hN20 : 0 ≤ N2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hσ := abs_signatureSigma_sub_le B hT hℓ u v ω
  have h4 : (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 4 ≤
      (C * r) ^ 4 * (N2 ^ 2 * E ^ 4) := by
    rw [← (by decide : Even 4).pow_abs]
    calc |signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω| ^ 4
        ≤ (C * r * Real.sqrt N2 * E) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hσ 4
      _ = (C * r) ^ 4 * ((Real.sqrt N2 ^ 2) ^ 2 * E ^ 4) := by ring
      _ = (C * r) ^ 4 * (N2 ^ 2 * E ^ 4) := by rw [Real.sq_sqrt hN20]
  have hamgm : N2 ^ 2 * E ^ 4 ≤ (N2 ^ 4 / h ^ 2 + h ^ 2 * (E ^ 4) ^ 2) / 2 := by
    have hkey : (N2 ^ 2 / h - h * E ^ 4) ^ 2 =
        N2 ^ 4 / h ^ 2 - 2 * (N2 ^ 2 * E ^ 4) + h ^ 2 * (E ^ 4) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (N2 ^ 2 / h - h * E ^ 4)]
  have hN8 : N2 ^ 4 ≤ ((d : ℝ) + 1) ^ 3 * S8 := sum_sq_pow_four_le _
  have hE8 : (E ^ 4) ^ 2 ≤ (Real.exp (16 * r * iu) + Real.exp (16 * r * iv)) / 2 := by
    have e1 : Real.exp (16 * r * iu) = Real.exp (8 * r * iu) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (16 * r * iv) = Real.exp (8 * r * iv) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : (E ^ 4) ^ 2 = Real.exp (8 * r * iu) * Real.exp (8 * r * iv) := by
      rw [← pow_mul, hE, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, e3]
    nlinarith [sq_nonneg (Real.exp (8 * r * iu) - Real.exp (8 * r * iv))]
  have hCr : 0 ≤ (C * r) ^ 4 := by positivity
  calc (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 4
      ≤ (C * r) ^ 4 * (N2 ^ 2 * E ^ 4) := h4
    _ ≤ (C * r) ^ 4 * ((N2 ^ 4 / h ^ 2 + h ^ 2 * (E ^ 4) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hamgm hCr
    _ ≤ (C * r) ^ 4 * ((((d : ℝ) + 1) ^ 3 * S8 / h ^ 2 +
          h ^ 2 * ((Real.exp (16 * r * iu) + Real.exp (16 * r * iv)) / 2)) / 2) := by
        gcongr
    _ = _ := by ring

/-! ## `HolderAdapted` for the signature volatility -/

/-- **`L⁴`-Hölder-`1/2` regularity of `σ = ⟨ℓ, Ŵ⟩` under H1–H2.** On every horizon `[0, t]`
the signature volatility of the Stratonovich setup over a Brownian driver is adapted to the
path filtration, in `L⁴`, and satisfies `E|σ_v - σ_u|⁴ ≤ K (v - u)²`. -/
theorem holderAdapted_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (t : ℝ) :
    ∃ K, HolderAdapted B (signatureSigma B hT ℓ) t K := by
  obtain ⟨C, r, hC, hr, hℓn⟩ := exists_levelNorm_le_geometric hw hℓ
  set c : ℝ := 16 * r with hc
  have hc0 : 0 ≤ c := by positivity
  set Eb : ℝ := 2 * ((d : ℝ) + 1) *
    Real.exp (c * ((d : ℝ) + 1) * t + (c * ((d : ℝ) + 1)) ^ 2 * t / 2) with hEb
  have hEb0 : 0 ≤ Eb := by positivity
  refine ⟨(C * r) ^ 4 / 2 * (((d : ℝ) + 1) ^ 4 * (t ^ 4 + gauss8Const) + Eb), ?_⟩
  have hmeasA : ∀ u, 0 ≤ u → AEStronglyMeasurable (signatureSigma B hT ℓ u) P := fun u hu =>
    ((measurable_signatureSigma_path B hT ℓ u ⟨u, hu, le_rfl⟩).mono
      ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable
  refine ⟨by have := gauss8Const_nonneg; positivity, fun u hu _ =>
    measurable_signatureSigma_path B hT ℓ u ⟨u, hu, le_rfl⟩, ?_, ?_⟩
  · intro u hu _
    have hint : Integrable (fun ω => Real.exp ((4 * r) * incrNorm B u ω)) P :=
      integrable_exp_mul_incrNorm B u (by positivity)
    have hg : MemLp (fun ω => Real.exp (r * incrNorm B u ω)) 4 P := by
      have hmeas : AEStronglyMeasurable (fun ω => Real.exp (r * incrNorm B u ω)) P :=
        ((measurable_incrNorm B u).const_mul r).exp.aestronglyMeasurable
      have h4 : MemLp (fun ω => Real.exp (r * incrNorm B u ω)) ((4 : ℕ) : ℝ≥0∞) P := by
        rw [← integrable_norm_rpow_iff hmeas (by simp) (by simp)]
        simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, Real.abs_exp]
        refine hint.congr (ae_of_all _ fun ω => ?_)
        simp only
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      exact_mod_cast h4
    refine (hg.const_mul C).mono' (hmeasA u hu) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_signatureSigma_le B hT hℓn u ω
  · intro u v hu huv hvt
    rcases huv.eq_or_lt with rfl | hlt
    · simp
    have hut : u ≤ t := huv.trans hvt
    set h : ℝ := v - u with hh
    have hh0 : 0 < h := sub_pos.mpr hlt
    set A : ℝ := (C * r) ^ 4 / 2 * (((d : ℝ) + 1) ^ 3 / h ^ 2) with hA
    set Bc : ℝ := (C * r) ^ 4 / 2 * (h ^ 2 / 2) with hBc
    have hA0 : 0 ≤ A := by positivity
    have hBc0 : 0 ≤ Bc := by positivity
    have hS8 : Integrable (fun ω => ∑ j,
        (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8) P :=
      integrable_finsetSum _ fun j _ => integrable_wAug_sub_pow8 B hu huv j
    have hEu : Integrable (fun ω => Real.exp (16 * r * incrNorm B u ω)) P :=
      integrable_exp_mul_incrNorm B u (by positivity)
    have hEv : Integrable (fun ω => Real.exp (16 * r * incrNorm B v ω)) P :=
      integrable_exp_mul_incrNorm B v (by positivity)
    have hIu : ∫ ω, Real.exp (16 * r * incrNorm B u ω) ∂P ≤ Eb :=
      integral_exp_mul_incrNorm_le B hc0 hu hut
    have hIv : ∫ ω, Real.exp (16 * r * incrNorm B v ω) ∂P ≤ Eb :=
      integral_exp_mul_incrNorm_le B hc0 (hu.trans huv) hvt
    have hI8 : ∑ j, ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 ∂P ≤
        ∑ _j : Fin (d + 1), (t ^ 4 + gauss8Const) * h ^ 4 :=
      Finset.sum_le_sum fun j _ => integral_wAug_sub_pow8_le B hu huv hvt j
    calc ∫ ω, (signatureSigma B hT ℓ v ω - signatureSigma B hT ℓ u ω) ^ 4 ∂P
        ≤ ∫ ω, (A * ∑ j, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 +
            Bc * Real.exp (16 * r * incrNorm B u ω) +
            Bc * Real.exp (16 * r * incrNorm B v ω)) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
            (((hS8.const_mul A).add (hEu.const_mul Bc)).add (hEv.const_mul Bc))
            (ae_of_all _ fun ω => signatureSigma_sub_pow_four_le B hT hℓn hh0 ω)
      _ = A * ∑ j, ∫ ω, (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 ∂P +
            Bc * ∫ ω, Real.exp (16 * r * incrNorm B u ω) ∂P +
            Bc * ∫ ω, Real.exp (16 * r * incrNorm B v ω) ∂P := by
          have hfirst : Integrable (fun ω => A * ∑ j,
              (MultiBrownian.wAug B v ω j - MultiBrownian.wAug B u ω j) ^ 8 +
              Bc * Real.exp (16 * r * incrNorm B u ω)) P :=
            (hS8.const_mul A).add (hEu.const_mul Bc)
          rw [integral_add hfirst (hEv.const_mul Bc),
            integral_add (hS8.const_mul A) (hEu.const_mul Bc), integral_const_mul,
            integral_const_mul, integral_const_mul,
            integral_finsetSum _ fun j _ => integrable_wAug_sub_pow8 B hu huv j]
      _ ≤ A * ∑ _j : Fin (d + 1), (t ^ 4 + gauss8Const) * h ^ 4 + Bc * Eb + Bc * Eb := by
          gcongr
      _ = (C * r) ^ 4 / 2 * (((d : ℝ) + 1) ^ 4 * (t ^ 4 + gauss8Const) + Eb) * h ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hA, hBc]
          push_cast
          field_simp
          ring

end SignatureVolatility
