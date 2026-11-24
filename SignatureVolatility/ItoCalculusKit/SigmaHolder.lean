module

public import SignatureVolatility.ItoCalculusKit.SigmaBounds
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity
public import SignatureVolatility.ProlongedBrownianSetup.SignatureOfBM


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

/-! ## `HolderAdapted` for the signature volatility -/

/-- **`L⁴`-Hölder-`1/2` regularity of `σ = ⟨ℓ, Ŵ⟩` under H1–H2.** On every horizon `[0, t]`
the signature volatility of the Stratonovich setup over a Brownian driver is adapted to the
path filtration, in `L⁴`, and satisfies `E|σ_v - σ_u|⁴ ≤ K (v - u)²`. -/
theorem holderAdapted_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (t : ℝ) :
    ∃ K, HolderAdapted B (signatureSigma B hT ℓ) t K := by
  obtain ⟨C, r, hC, hr, hℓn⟩ := exists_levelNorm_le_geometric hw hℓ
  obtain ⟨K, hK, hKb⟩ := dualPairing_paperSig2_incr (P := P) B hC hr hℓn (q := 2) le_rfl
    (le_max_right t 0)
  obtain ⟨M, -, hM⟩ := dualPairing_paperSig2_moment (P := P) B hC hr hℓn (q := 2) le_rfl
    (t := max t 0)
  refine ⟨K, hK, fun u hu _ => measurable_signatureSigma_path B hT ℓ u ⟨u, hu, le_rfl⟩,
    fun u hu hut => (hM u hu (hut.trans (le_max_left _ _))).2.1,
    fun u v hu huv hvt => (hKb u v hu huv (hvt.trans (le_max_left _ _))).2⟩


end SignatureVolatility
