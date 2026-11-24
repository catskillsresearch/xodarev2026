module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Degree-≤4 polynomial bounded above by 0 and below by `L - 2 log(1+s₀|x|)` on `(-∞,0]` is constant
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace SignatureVolatility

private lemma log_div_nat_tendsto_zero {s₀ : ℝ} (hs₀ : 0 < s₀) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (1 + s₀ * (n : ℝ)) / (n : ℝ) ^ k) atTop (𝓝 0) := by
  have hlog_sqrt : ∀ u : ℝ, 0 < u → Real.log u ≤ 2 * Real.sqrt u := fun u hu => by
    have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
    have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
      have hpow := Real.log_pow (Real.sqrt u) 2
      simpa [Real.sq_sqrt hu.le] using hpow
    linarith
  have hlim_top : Tendsto (fun n : ℕ => 2 * Real.sqrt (1 / (n : ℝ) ^ 2 + s₀ / (n : ℝ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have := tendsto_const_nhds (x := (1 : ℝ)) |>.div_atTop
        ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n : ℕ => s₀ / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat s₀
    have h3 := ((h1.add h2).sqrt).const_mul 2
    simpa using h3
  have harg_ge_one : ∀ n : ℕ, (1 : ℝ) ≤ 1 + s₀ * (n : ℝ) := fun n =>
    le_add_of_nonneg_right (mul_nonneg hs₀.le (Nat.cast_nonneg n))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_top ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.log_nonneg (harg_ge_one n)) (pow_nonneg (Nat.cast_nonneg n) k)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hpow_ge : (n : ℝ) ≤ (n : ℝ) ^ k := by
      simpa using pow_le_pow_right₀ hn1 hk
    have hlog0 : 0 ≤ Real.log (1 + s₀ * (n : ℝ)) := Real.log_nonneg (harg_ge_one n)
    have harg_pos : 0 < 1 + s₀ * (n : ℝ) :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs₀.le (Nat.cast_nonneg n))
    calc Real.log (1 + s₀ * (n : ℝ)) / (n : ℝ) ^ k
        ≤ Real.log (1 + s₀ * (n : ℝ)) / (n : ℝ) :=
          div_le_div_of_nonneg_left hlog0 hn_pos hpow_ge
      _ ≤ (2 * Real.sqrt (1 + s₀ * (n : ℝ))) / (n : ℝ) :=
          div_le_div_of_nonneg_right (hlog_sqrt _ harg_pos) hn_pos.le
      _ = 2 * Real.sqrt (1 / (n : ℝ) ^ 2 + s₀ / (n : ℝ)) := by
          calc
            (2 * Real.sqrt (1 + s₀ * (n : ℝ))) / (n : ℝ)
              = 2 * (Real.sqrt (1 + s₀ * (n : ℝ)) / Real.sqrt ((n : ℝ) ^ 2)) := by
                rw [mul_div_assoc, Real.sqrt_sq hn_pos.le]
            _ = 2 * Real.sqrt ((1 + s₀ * (n : ℝ)) / (n : ℝ) ^ 2) := by
                rw [Real.sqrt_div harg_pos.le]
            _ = 2 * Real.sqrt (1 / (n : ℝ) ^ 2 + s₀ / (n : ℝ)) := by
                congr 2; field_simp

/-- A degree-`≤ 4` polynomial bounded above by `0` and below by
`L - 2 log(1 + s₀ |x|)` on `(-∞, 0]` is constant. This is the Part 3
drop-in replacement for `poly4_const_of_bdd_nonpos`; the main theorem
statement is unchanged. -/
lemma poly4_const_of_log_bdd_nonpos {a₀ a₁ a₂ a₃ a₄ L s₀ : ℝ} (hs₀ : 0 < s₀)
    (hbdd : ∀ x : ℝ, x ≤ 0 →
      L - 2 * Real.log (1 + s₀ * |x|) ≤
        a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ∧
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ≤ 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have habs : ∀ n : ℕ,
      |a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
        a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4| ≤
      |L| + 2 * Real.log (1 + s₀ * (n : ℝ)) := by
    intro n
    have h := hbdd (-(n : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hnabs : |(-(n : ℝ))| = (n : ℝ) := by
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg (n : ℕ))]
    have hL : L - 2 * Real.log (1 + s₀ * (n : ℝ)) ≤
        a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4 ∧
        a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4 ≤ 0 := by
      convert h using 1
      rw [hnabs]
    rw [abs_le]
    have hlog0 : 0 ≤ Real.log (1 + s₀ * (n : ℝ)) :=
      Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg hs₀.le (Nat.cast_nonneg n)))
    exact ⟨by linarith [neg_abs_le L], by linarith [abs_nonneg L]⟩
  have hpow0 : ∀ (k : ℕ), 0 < k → ∀ c : ℝ,
      Tendsto (fun n : ℕ => c / ((n : ℝ) ^ k)) atTop (𝓝 0) := fun k hk c => by
    have h := tendsto_const_nhds (x := c) |>.div_atTop
      ((tendsto_pow_atTop (Nat.ne_of_gt hk)).comp tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using h
  have hbound0 : ∀ (k : ℕ), 0 < k →
      Tendsto (fun n : ℕ => (|L| + 2 * Real.log (1 + s₀ * (n : ℝ))) / (n : ℝ) ^ k)
        atTop (𝓝 0) := fun k hk => by
    have h := (hpow0 k hk |L|).add ((log_div_nat_tendsto_zero hs₀ k hk).const_mul 2)
    rw [mul_zero, add_zero] at h
    refine h.congr fun n => by ring
  have ha4 : a₄ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4) / (n : ℝ) ^ 4|) atTop (𝓝 |a₄|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 4 - a₁ / (n : ℝ) ^ 3 + a₂ / (n : ℝ) ^ 2 - a₃ / (n : ℝ) ^ 1 + a₄)
          atTop (𝓝 (0 - 0 + 0 - 0 + a₄)) :=
        ((((hpow0 4 (by norm_num) a₀).sub (hpow0 3 (by norm_num) a₁)).add
          (hpow0 2 (by norm_num) a₂)).sub (hpow0 1 (by norm_num) a₃)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp <;> try ring
    have hle : |a₄| ≤ 0 := le_of_tendsto_of_tendsto hlim (hbound0 4 (by norm_num)) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)]
      exact div_le_div_of_nonneg_right (habs n) (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha4
  have ha3 : a₃ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3) / (n : ℝ) ^ 3|) atTop (𝓝 |-a₃|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 3 - a₁ / (n : ℝ) ^ 2 + a₂ / (n : ℝ) ^ 1 + (-a₃))
          atTop (𝓝 (0 - 0 + 0 + (-a₃))) :=
        (((hpow0 3 (by norm_num) a₀).sub (hpow0 2 (by norm_num) a₁)).add
          (hpow0 1 (by norm_num) a₂)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp <;> try ring
    have hle : |-a₃| ≤ 0 := le_of_tendsto_of_tendsto hlim (hbound0 3 (by norm_num)) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    simpa [abs_neg] using le_antisymm hle (abs_nonneg _)
  subst ha3
  have ha2 : a₂ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2) / (n : ℝ) ^ 2|) atTop (𝓝 |a₂|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 2 - a₁ / (n : ℝ) ^ 1 + a₂)
          atTop (𝓝 (0 - 0 + a₂)) :=
        ((hpow0 2 (by norm_num) a₀).sub (hpow0 1 (by norm_num) a₁)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp <;> try ring
    have hle : |a₂| ≤ 0 := le_of_tendsto_of_tendsto hlim (hbound0 2 (by norm_num)) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha2
  have ha1 : a₁ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ))) / (n : ℝ) ^ 1|) atTop (𝓝 |-a₁|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 1 + (-a₁)) atTop (𝓝 (0 + (-a₁))) :=
        (hpow0 1 (by norm_num) a₀).add tendsto_const_nhds
      simp only [zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp <;> try ring
    have hle : |-a₁| ≤ 0 := le_of_tendsto_of_tendsto hlim (hbound0 1 (by norm_num)) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 1)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    exact abs_eq_zero.mp (by simpa [abs_neg] using le_antisymm hle (abs_nonneg _))
  exact ⟨ha1, rfl, rfl, rfl⟩

end SignatureVolatility
