module

public import SignatureVolatility.ItoCalculusKit.GridDoob

@[expose] public section

open Filter Topology Finset

namespace SignatureVolatility

/-!
# Pathwise control of the Doléans–Itô error

Deterministic analysis: with `xᵢ = gᵢ wᵢ + aᵢ - dqᵢ / 2`,
`∑ zᵢ (e^{xᵢ} - 1 - gᵢ wᵢ) → 0` provided `∑ zᵢ aᵢ → 0`, `∑ zᵢ gᵢ² (wᵢ² - δ) → 0`, `∑ aᵢ² → 0`,
`∑ wᵢ² → t`, `max |wᵢ| → 0`, `0 ≤ zᵢ ≤ M`, `|gᵢ| ≤ G`, `0 ≤ dqᵢ`, `∑ dqᵢ ≤ Q` and
`|gᵢ² δ - dqᵢ| ≤ δ εₙ` with `εₙ → 0` (`tendsto_doleansError`).
-/

lemma abs_add8_le (a b c d e f g h : ℝ) :
    |a + b + c + d + e + f + g + h| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| := by
  have h1 := abs_add_le (a + b + c + d + e + f + g) h
  have h2 := abs_add_le (a + b + c + d + e + f) g
  have h3 := abs_add_le (a + b + c + d + e) f
  have h4 := abs_add_le (a + b + c + d) e
  have h5 := abs_add_le (a + b + c) d
  have h6 := abs_add_le (a + b) c
  have h7 := abs_add_le a b
  linarith

lemma abs_exp_sub_quad_le {x μ : ℝ} (hx : |x| ≤ μ) (hμ : μ ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ μ * x ^ 2 := by
  have hx1 : |x| ≤ 1 := hx.trans hμ
  have h := Real.exp_bound hx1 (n := 3) (by norm_num)
  have hs : ∑ m ∈ range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  refine h.trans ?_
  have hc : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ) ≤ 1 := by
    norm_num [Nat.factorial]
  have h3 : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ', sq_abs]
  calc |x| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ))
      ≤ |x| ^ 3 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast hc
    _ = |x| * x ^ 2 := by rw [mul_one, h3]
    _ ≤ μ * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- Per-cell remainder after removing the martingale parts. -/
lemma abs_doleansRem_le {g w a dq δ μ : ℝ} (hdq : 0 ≤ dq)
    (hx : |g * w + a - dq / 2| ≤ μ) (hμ : μ ≤ 1) :
    |Real.exp (g * w + a - dq / 2) - 1 - g * w - a - g ^ 2 * (w ^ 2 - δ) / 2| ≤
      |g ^ 2 * δ - dq| / 2 + |g * w| * |a| + a ^ 2 / 2 + |g * w| * dq / 2 + |a| * dq / 2 +
        dq ^ 2 / 8 + μ * (g * w + a - dq / 2) ^ 2 := by
  set x := g * w + a - dq / 2 with hxdef
  have hr := abs_exp_sub_quad_le hx hμ
  have heq : Real.exp x - 1 - g * w - a - g ^ 2 * (w ^ 2 - δ) / 2 =
      (g ^ 2 * δ - dq) / 2 + (g * w) * a + a ^ 2 / 2 + (-(g * w) * dq / 2) + (-a * dq / 2) +
        dq ^ 2 / 8 + 0 + (Real.exp x - (1 + x + x ^ 2 / 2)) := by
    rw [hxdef]; ring
  rw [heq]
  refine (abs_add8_le _ _ _ _ _ _ _ _).trans ?_
  have e1 : |(g ^ 2 * δ - dq) / 2| = |g ^ 2 * δ - dq| / 2 := by
    rw [abs_div, abs_two]
  have e2 : |g * w * a| = |g * w| * |a| := abs_mul _ _
  have e3 : |a ^ 2 / 2| = a ^ 2 / 2 := abs_of_nonneg (by positivity)
  have e4 : |-(g * w) * dq / 2| = |g * w| * dq / 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hdq, abs_two]
  have e5 : |-a * dq / 2| = |a| * dq / 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hdq, abs_two]
  have e6 : |dq ^ 2 / 8| = dq ^ 2 / 8 := abs_of_nonneg (by positivity)
  rw [e1, e2, e3, e4, e5, e6, abs_zero]
  linarith

/-- **Pathwise Doléans–Itô error bound.** -/
theorem tendsto_doleansError {t M G Q : ℝ} (ht : 0 ≤ t) (hG0 : 0 ≤ G)
    (z a w g dq : ℕ → ℕ → ℝ) {ε β : ℕ → ℝ}
    (hz : ∀ n i, i < n + 1 → 0 ≤ z n i ∧ z n i ≤ M)
    (hg : ∀ n i, i < n + 1 → |g n i| ≤ G)
    (hdq0 : ∀ n i, i < n + 1 → 0 ≤ dq n i)
    (hQ : ∀ n, ∑ i ∈ range (n + 1), dq n i ≤ Q)
    (hdq : ∀ n i, i < n + 1 →
      |g n i ^ 2 * (t / ((n + 1 : ℕ) : ℝ)) - dq n i| ≤ t / ((n + 1 : ℕ) : ℝ) * ε n)
    (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hw : ∀ n i, i < n + 1 → |w n i| ≤ β n) (hβ : Tendsto β atTop (𝓝 0))
    (hW : Tendsto (fun n => ∑ i ∈ range (n + 1), w n i ^ 2) atTop (𝓝 t))
    (hA : Tendsto (fun n => ∑ i ∈ range (n + 1), a n i ^ 2) atTop (𝓝 0))
    (h1 : Tendsto (fun n => ∑ i ∈ range (n + 1), z n i * a n i) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∑ i ∈ range (n + 1),
      z n i * (g n i ^ 2 * (w n i ^ 2 - t / ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ range (n + 1),
      z n i * (Real.exp (g n i * w n i + a n i - dq n i / 2) - 1 - g n i * w n i))
      atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (hz 0 0 (by norm_num)).1.trans (hz 0 0 (by norm_num)).2
  set δ : ℕ → ℝ := fun n => t / ((n + 1 : ℕ) : ℝ) with hδdef
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => by simp only [hδdef]; positivity
  have hδsum : ∀ n, ∑ _i ∈ range (n + 1), δ n = t := fun n => by
    have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [sum_const, card_range, nsmul_eq_mul]
    simp only [hδdef]
    exact mul_div_cancel₀ t hN
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
    exact h.congr fun n => by simp [hδdef]
  set η : ℕ → ℝ := fun n => δ n * (G ^ 2 + ε n) with hηdef
  have hη0 : ∀ n, 0 ≤ η n := fun n => mul_nonneg (hδ0 n) (by have := hε0 n; positivity)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h := hδlim.mul ((tendsto_const_nhds (x := G ^ 2)).add hε)
    simpa [hηdef] using h
  have hg2 : ∀ n i, i < n + 1 → g n i ^ 2 ≤ G ^ 2 := fun n i hi => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hg n i hi) 2
  have hdqη : ∀ n i, i < n + 1 → dq n i ≤ η n := fun n i hi => by
    have h := (abs_le.mp (hdq n i hi)).1
    have h2 : g n i ^ 2 * δ n ≤ G ^ 2 * δ n := mul_le_mul_of_nonneg_right (hg2 n i hi) (hδ0 n)
    simp only [hηdef]
    simp only [hδdef] at h h2 ⊢
    nlinarith
  set A2 : ℕ → ℝ := fun n => ∑ i ∈ range (n + 1), a n i ^ 2 with hA2
  set W2 : ℕ → ℝ := fun n => ∑ i ∈ range (n + 1), w n i ^ 2 with hW2
  set Y2 : ℕ → ℝ := fun n => ∑ i ∈ range (n + 1), (g n i * w n i) ^ 2 with hY2
  set D2 : ℕ → ℝ := fun n => ∑ i ∈ range (n + 1), dq n i ^ 2 with hD2
  have hY2le : ∀ n, Y2 n ≤ G ^ 2 * W2 n := fun n => by
    simp only [hY2, hW2, mul_sum]
    exact sum_le_sum fun i hi => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hg2 n i (mem_range.mp hi)) (sq_nonneg _)
  have hD2le : ∀ n, D2 n ≤ η n * Q := fun n => by
    calc D2 n = ∑ i ∈ range (n + 1), dq n i * dq n i := by simp only [hD2, sq]
      _ ≤ ∑ i ∈ range (n + 1), η n * dq n i := sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hdqη n i (mem_range.mp hi)) (hdq0 n i (mem_range.mp hi))
      _ = η n * ∑ i ∈ range (n + 1), dq n i := by rw [mul_sum]
      _ ≤ η n * Q := mul_le_mul_of_nonneg_left (hQ n) (hη0 n)
  set μ : ℕ → ℝ := fun n => G * β n + Real.sqrt (A2 n) + η n / 2 with hμdef
  have hx : ∀ n i, i < n + 1 → |g n i * w n i + a n i - dq n i / 2| ≤ μ n := by
    intro n i hi
    have ha : |a n i| ≤ Real.sqrt (A2 n) := Real.abs_le_sqrt
      (single_le_sum (f := fun i => a n i ^ 2) (fun j _ => sq_nonneg _) (mem_range.mpr hi))
    have hy : |g n i * w n i| ≤ G * β n := by
      rw [abs_mul]; exact mul_le_mul (hg n i hi) (hw n i hi) (abs_nonneg _) hG0
    have hd : |dq n i / 2| ≤ η n / 2 := by
      rw [abs_div, abs_two, abs_of_nonneg (hdq0 n i hi)]
      linarith [hdqη n i hi]
    calc |g n i * w n i + a n i - dq n i / 2|
        ≤ |g n i * w n i| + |a n i| + |dq n i / 2| := by
          have h1 := abs_sub (g n i * w n i + a n i) (dq n i / 2)
          have h2 := abs_add_le (g n i * w n i) (a n i)
          linarith
      _ ≤ μ n := by simp only [hμdef]; linarith
  have hμlim : Tendsto μ atTop (𝓝 0) := by
    have h := ((hβ.const_mul G).add hA.sqrt).add (hηlim.div_const 2)
    simpa [hμdef, hA2] using h
  -- the bound
  set Bd : ℕ → ℝ := fun n =>
    |∑ i ∈ range (n + 1), z n i * a n i| +
      |∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))| / 2 +
      M * (t * ε n / 2 + Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (A2 n) + A2 n / 2 +
        Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (η n * Q) / 2 +
        Real.sqrt (A2 n) * Real.sqrt (η n * Q) / 2 + η n * Q / 8 +
        μ n * (3 * (G ^ 2 * W2 n + A2 n + η n * Q / 4))) with hBd
  have hBlim : Tendsto Bd atTop (𝓝 0) := by
    have hW' : Tendsto W2 atTop (𝓝 t) := hW
    have hA' : Tendsto A2 atTop (𝓝 0) := hA
    have hηQ := hηlim.mul_const Q
    have hGW := (hW'.const_mul (G ^ 2)).sqrt
    have k1 := ((hε.const_mul t).div_const 2).add (hGW.mul hA'.sqrt)
    have k2 := (k1.add (hA'.div_const 2)).add ((hGW.mul hηQ.sqrt).div_const 2)
    have k3 := (k2.add ((hA'.sqrt.mul hηQ.sqrt).div_const 2)).add (hηQ.div_const 8)
    have k4 := hμlim.mul ((((hW'.const_mul (G ^ 2)).add hA').add (hηQ.div_const 4)).const_mul 3)
    have k5 := (k3.add k4).const_mul M
    have h := (h1.abs.add (h2.abs.div_const 2)).add k5
    simpa [hBd, hδdef] using h
  refine squeeze_zero_norm' ?_ hBlim
  filter_upwards [(hμlim.eventually (ge_mem_nhds (zero_lt_one' ℝ)))] with n hμn
  rw [Real.norm_eq_abs]
  have hsplit : ∑ i ∈ range (n + 1),
      z n i * (Real.exp (g n i * w n i + a n i - dq n i / 2) - 1 - g n i * w n i) =
      ∑ i ∈ range (n + 1), z n i * a n i +
        (∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))) / 2 +
        ∑ i ∈ range (n + 1), z n i * (Real.exp (g n i * w n i + a n i - dq n i / 2) - 1 -
          g n i * w n i - a n i - g n i ^ 2 * (w n i ^ 2 - δ n) / 2) := by
    rw [sum_div, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  set R : ℕ → ℝ := fun i => Real.exp (g n i * w n i + a n i - dq n i / 2) - 1 -
    g n i * w n i - a n i - g n i ^ 2 * (w n i ^ 2 - δ n) / 2 with hR
  have hRsum : |∑ i ∈ range (n + 1), z n i * R i| ≤ M * ∑ i ∈ range (n + 1), |R i| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hzi := hz n i (mem_range.mp hi)
    rw [abs_mul, abs_of_nonneg hzi.1]
    exact mul_le_mul_of_nonneg_right hzi.2 (abs_nonneg _)
  have hRi : ∀ i ∈ range (n + 1), |R i| ≤
      |g n i ^ 2 * δ n - dq n i| / 2 + |g n i * w n i| * |a n i| + a n i ^ 2 / 2 +
        |g n i * w n i| * dq n i / 2 + |a n i| * dq n i / 2 + dq n i ^ 2 / 8 +
        μ n * (3 * ((g n i * w n i) ^ 2 + a n i ^ 2 + dq n i ^ 2 / 4)) := by
    intro i hi
    have hi' := mem_range.mp hi
    have h := abs_doleansRem_le (δ := δ n) (hdq0 n i hi') (hx n i hi') hμn
    have hμ0 : 0 ≤ μ n := (abs_nonneg _).trans (hx n i hi')
    have hsq : (g n i * w n i + a n i - dq n i / 2) ^ 2 ≤
        3 * ((g n i * w n i) ^ 2 + a n i ^ 2 + dq n i ^ 2 / 4) := by
      nlinarith [sq_nonneg (g n i * w n i - a n i), sq_nonneg (g n i * w n i + dq n i / 2),
        sq_nonneg (a n i + dq n i / 2)]
    have := mul_le_mul_of_nonneg_left hsq hμ0
    simp only [hR]
    linarith
  have hS1 : ∑ i ∈ range (n + 1), |g n i ^ 2 * δ n - dq n i| / 2 ≤ t * ε n / 2 := by
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc ∑ i ∈ range (n + 1), |g n i ^ 2 * δ n - dq n i|
        ≤ ∑ _i ∈ range (n + 1), δ n * ε n := sum_le_sum fun i hi => hdq n i (mem_range.mp hi)
      _ = t * ε n := by rw [← sum_mul, hδsum]
  have hCS : ∀ f h : ℕ → ℝ, ∑ i ∈ range (n + 1), |f i| * |h i| ≤
      Real.sqrt (∑ i ∈ range (n + 1), f i ^ 2) * Real.sqrt (∑ i ∈ range (n + 1), h i ^ 2) := by
    intro f h
    have := Real.sum_mul_le_sqrt_mul_sqrt (range (n + 1)) (fun i => |f i|) (fun i => |h i|)
    simpa only [sq_abs] using this
  have hS2 : ∑ i ∈ range (n + 1), |g n i * w n i| * |a n i| ≤
      Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (A2 n) :=
    (hCS (fun i => g n i * w n i) (a n)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hY2le n)) (Real.sqrt_nonneg _))
  have hdqabs : ∀ i ∈ range (n + 1), dq n i = |dq n i| := fun i hi =>
    (abs_of_nonneg (hdq0 n i (mem_range.mp hi))).symm
  have hS4 : ∑ i ∈ range (n + 1), |g n i * w n i| * dq n i / 2 ≤
      Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (η n * Q) / 2 := by
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    rw [sum_congr rfl fun i hi => by rw [hdqabs i hi]]
    exact (hCS (fun i => g n i * w n i) (dq n)).trans
      (mul_le_mul (Real.sqrt_le_sqrt (hY2le n)) (Real.sqrt_le_sqrt (hD2le n))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hS5 : ∑ i ∈ range (n + 1), |a n i| * dq n i / 2 ≤
      Real.sqrt (A2 n) * Real.sqrt (η n * Q) / 2 := by
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    rw [sum_congr rfl fun i hi => by rw [hdqabs i hi]]
    exact (hCS (a n) (dq n)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hD2le n)) (Real.sqrt_nonneg _))
  have hμ0 : 0 ≤ μ n := (abs_nonneg _).trans (hx n 0 (by omega))
  have hS7 : ∑ i ∈ range (n + 1), μ n * (3 * ((g n i * w n i) ^ 2 + a n i ^ 2 + dq n i ^ 2 / 4))
      ≤ μ n * (3 * (G ^ 2 * W2 n + A2 n + η n * Q / 4)) := by
    rw [← mul_sum, ← mul_sum, sum_add_distrib, sum_add_distrib, ← sum_div]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hμ0
    have := hY2le n
    have := hD2le n
    simp only [hY2, hD2, hA2] at *
    linarith
  have hS6 : ∑ i ∈ range (n + 1), dq n i ^ 2 / 8 ≤ η n * Q / 8 := by
    rw [← sum_div]; exact div_le_div_of_nonneg_right (hD2le n) (by norm_num)
  have hS3 : ∑ i ∈ range (n + 1), a n i ^ 2 / 2 = A2 n / 2 := by rw [← sum_div]
  have hsumR := sum_le_sum hRi
  simp only [sum_add_distrib] at hsumR
  have hRtot : ∑ i ∈ range (n + 1), |R i| ≤ t * ε n / 2 +
      Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (A2 n) + A2 n / 2 +
      Real.sqrt (G ^ 2 * W2 n) * Real.sqrt (η n * Q) / 2 +
      Real.sqrt (A2 n) * Real.sqrt (η n * Q) / 2 + η n * Q / 8 +
      μ n * (3 * (G ^ 2 * W2 n + A2 n + η n * Q / 4)) := by
    linarith
  have hfin := hRsum.trans (mul_le_mul_of_nonneg_left hRtot hM0)
  have htri := abs_add_le (∑ i ∈ range (n + 1), z n i * a n i +
      (∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))) / 2)
      (∑ i ∈ range (n + 1), z n i * R i)
  have htri2 := abs_add_le (∑ i ∈ range (n + 1), z n i * a n i)
      ((∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))) / 2)
  have hdiv : |(∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))) / 2| =
      |∑ i ∈ range (n + 1), z n i * (g n i ^ 2 * (w n i ^ 2 - δ n))| / 2 := by
    rw [abs_div, abs_two]
  simp only [hBd]
  linarith

end SignatureVolatility
