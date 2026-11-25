module

public import SignatureVolatility.SignatureRiccatiKit.BarrierU
public import SignatureVolatility.SignatureRiccatiKit.LintegralExpShifted
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ItoCalculusKit.CrossVariation
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto

/-!
# B4b. 1D Itô on `barrierU` plus the Doléans bound gives `v₁ x ≤ exp(u(0,x))`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped ENNReal NNReal
set_option maxHeartbeats 800000


namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Part 1: Partial derivatives & continuity of `barrierU` -/

private def barrierUr (s₀ β A r y : ℝ) : ℝ :=
  if A / s₀ < y ∧ A / y < s₀ - r then 3 * β * (s₀ - r - A / y) ^ 2 else 0

private def barrierUy (s₀ β A r y : ℝ) : ℝ :=
  if A / s₀ < y ∧ A / y < s₀ - r then -3 * β * (s₀ - r - A / y) ^ 2 * (A / y ^ 2) else 0

private def barrierUyy (s₀ β A r y : ℝ) : ℝ :=
  if A / s₀ < y ∧ A / y < s₀ - r then
    -6 * β * (s₀ - r - A / y) * (A / y ^ 2) ^ 2 + 6 * β * (s₀ - r - A / y) ^ 2 * (A / y ^ 3)
  else 0

/-- Clamped representation of `barrierU` and its partials on `[0, s₀] × ℝ` (no `let` in statement). -/
private lemma barrierU_eq_clamped {s₀ β A r y : ℝ} (hs₀ : 0 < s₀) (hA : 0 < A)
    (hr0 : 0 ≤ r) (_hrs : r ≤ s₀) :
    barrierU s₀ β A r y = -β * (max (s₀ - r - A / max y (A / (2 * s₀))) 0) ^ 3 ∧
    barrierUr s₀ β A r y = 3 * β * (max (s₀ - r - A / max y (A / (2 * s₀))) 0) ^ 2 ∧
    barrierUy s₀ β A r y =
      -3 * β * (max (s₀ - r - A / max y (A / (2 * s₀))) 0) ^ 2 *
        (A / (max y (A / (2 * s₀))) ^ 2) ∧
    barrierUyy s₀ β A r y =
      -6 * β * (max (s₀ - r - A / max y (A / (2 * s₀))) 0) *
          (A / (max y (A / (2 * s₀))) ^ 2) ^ 2 +
        6 * β * (max (s₀ - r - A / max y (A / (2 * s₀))) 0) ^ 2 *
          (A / (max y (A / (2 * s₀))) ^ 3) := by
  have hhalf : A / (2 * s₀) < A / s₀ :=
    div_lt_div_of_pos_left hA hs₀ (lt_mul_of_one_lt_left hs₀ one_lt_two)
  by_cases h1 : A / s₀ < y
  · have hy' : max y (A / (2 * s₀)) = y := max_eq_left (hhalf.le.trans h1.le)
    rw [hy']
    by_cases h2 : A / y < s₀ - r
    · have hv : max (s₀ - r - A / y) 0 = s₀ - r - A / y := max_eq_left (sub_nonneg.mpr h2.le)
      simp [barrierU, barrierUr, barrierUy, barrierUyy, h1, h2, and_self, hv]
    · have hv : max (s₀ - r - A / y) 0 = 0 := max_eq_right (sub_nonpos.mpr (not_lt.mp h2))
      simp [barrierU, barrierUr, barrierUy, barrierUyy, h1, h2, hv]
  · have hy'_le : max y (A / (2 * s₀)) ≤ A / s₀ := max_le (not_lt.mp h1) hhalf.le
    have hy'_pos : 0 < max y (A / (2 * s₀)) :=
      lt_of_lt_of_le (div_pos hA (by positivity)) (le_max_right _ _)
    have hAy' : s₀ ≤ A / max y (A / (2 * s₀)) := by
      rw [le_div_iff₀ hy'_pos]
      have := (le_div_iff₀ hs₀).mp hy'_le
      linarith
    have hv : max (s₀ - r - A / max y (A / (2 * s₀))) 0 = 0 := max_eq_right (by linarith)
    simp [barrierU, barrierUr, barrierUy, barrierUyy, h1, hv]

/-- Direct representation when `A / (2 s₀) ≤ y` (no `max y ...` at all). -/
private lemma barrierU_of_ge_half {s₀ β A r y : ℝ} (hs₀ : 0 < s₀) (hA : 0 < A)
    (hr0 : 0 ≤ r) (hrs : r ≤ s₀) (hy : A / (2 * s₀) ≤ y) :
    barrierU s₀ β A r y = -β * (max (s₀ - r - A / y) 0) ^ 3 ∧
    barrierUr s₀ β A r y = 3 * β * (max (s₀ - r - A / y) 0) ^ 2 ∧
    barrierUy s₀ β A r y = -3 * β * (max (s₀ - r - A / y) 0) ^ 2 * (A / y ^ 2) ∧
    barrierUyy s₀ β A r y =
      -6 * β * (max (s₀ - r - A / y) 0) * (A / y ^ 2) ^ 2 +
        6 * β * (max (s₀ - r - A / y) 0) ^ 2 * (A / y ^ 3) := by
  have h := barrierU_eq_clamped hs₀ hA hr0 hrs (β := β) (y := y)
  rwa [max_eq_left hy] at h

/-! ### Part 2: Modular, purely algebraic Taylor remainder for `barrierU` (zero big `nlinarith`!) -/

private lemma eta_cube_taylor {β : ℝ} (hβ : 0 < β) (ξ₁ ξ₂ : ℝ) :
    |(-β * (max ξ₂ 0) ^ 3) - (-β * (max ξ₁ 0) ^ 3) -
      (-3 * β * (max ξ₁ 0) ^ 2) * (ξ₂ - ξ₁) -
      (1 / 2 : ℝ) * (-6 * β * (max ξ₁ 0)) * (ξ₂ - ξ₁) ^ 2| ≤
    β * |ξ₂ - ξ₁| ^ 3 := by
  by_cases h1 : 0 ≤ ξ₁ <;> by_cases h2 : 0 ≤ ξ₂
  · rw [max_eq_left h1, max_eq_left h2]
    have heq : -β * ξ₂ ^ 3 - -β * ξ₁ ^ 3 - -3 * β * ξ₁ ^ 2 * (ξ₂ - ξ₁) -
        1 / 2 * (-6 * β * ξ₁) * (ξ₂ - ξ₁) ^ 2 = -β * (ξ₂ - ξ₁) ^ 3 := by ring
    rw [heq, abs_mul, abs_neg, abs_of_pos hβ, abs_pow]
  · rw [max_eq_left h1, max_eq_right (not_le.mp h2).le]
    have heq : -β * 0 ^ 3 - -β * ξ₁ ^ 3 - -3 * β * ξ₁ ^ 2 * (ξ₂ - ξ₁) -
        1 / 2 * (-6 * β * ξ₁) * (ξ₂ - ξ₁) ^ 2 = β * (ξ₂ ^ 3 - (ξ₂ - ξ₁) ^ 3) := by ring
    rw [heq, abs_mul, abs_of_pos hβ]
    have hneg2 : ξ₂ ≤ 0 := (not_le.mp h2).le
    have hneg_d : ξ₂ - ξ₁ ≤ 0 := by linarith
    have hcube_le : (ξ₂ - ξ₁) ^ 3 ≤ ξ₂ ^ 3 := by
      have hfac : ξ₂ ^ 3 - (ξ₂ - ξ₁) ^ 3 = ξ₁ * (ξ₂ ^ 2 + ξ₂ * (ξ₂ - ξ₁) + (ξ₂ - ξ₁) ^ 2) := by ring
      have hnn : 0 ≤ ξ₂ ^ 2 + ξ₂ * (ξ₂ - ξ₁) + (ξ₂ - ξ₁) ^ 2 :=
        add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg_of_nonpos_of_nonpos hneg2 hneg_d)) (sq_nonneg _)
      linarith [mul_nonneg h1 hnn]
    have hcube2 : ξ₂ ^ 3 ≤ 0 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg2
    rw [abs_of_nonneg (sub_nonneg.mpr hcube_le)]
    have habs_d : |ξ₂ - ξ₁| = -(ξ₂ - ξ₁) := abs_of_nonpos hneg_d
    rw [habs_d]
    have hneg3 : (-(ξ₂ - ξ₁)) ^ 3 = -((ξ₂ - ξ₁) ^ 3) := by ring
    calc β * (ξ₂ ^ 3 - (ξ₂ - ξ₁) ^ 3)
        ≤ β * (0 - (ξ₂ - ξ₁) ^ 3) := by gcongr
      _ = β * (-((ξ₂ - ξ₁) ^ 3)) := by ring
      _ = β * (-(ξ₂ - ξ₁)) ^ 3 := by rw [hneg3]
  · rw [max_eq_right (not_le.mp h1).le, max_eq_left h2]
    simp only [zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, sub_zero, abs_mul, abs_neg, abs_of_pos hβ, abs_pow, abs_of_nonneg h2]
    have hle : ξ₂ ≤ |ξ₂ - ξ₁| := by rw [abs_of_nonneg (by linarith)]; linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 hle 3) hβ.le
  · rw [max_eq_right (not_le.mp h1).le, max_eq_right (not_le.mp h2).le]
    simp only [zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, sub_zero, abs_zero]
    positivity

private lemma add_cube_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * a ^ 3 + 4 * b ^ 3 := by
  have h : 4 * a ^ 3 + 4 * b ^ 3 - (a + b) ^ 3 = 3 * (a + b) * (a - b) ^ 2 := by ring
  have hnn : 0 ≤ 3 * (a + b) * (a - b) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (add_nonneg ha hb)) (sq_nonneg _)
  linarith

/-- Exact algebraic splitting of the Taylor remainder in Regime 1 (`y₁, y₂ ≥ A / (2 s₀)`). -/
private lemma barrierU_taylor_split {s₀ β A r₁ r₂ y₁ y₂ : ℝ} (hs₀ : 0 < s₀) (hA : 0 < A)
    (hr1 : 0 ≤ r₁) (hr12 : r₁ ≤ r₂) (hr2 : r₂ ≤ s₀)
    (hy1 : A / (2 * s₀) ≤ y₁) (hy2 : A / (2 * s₀) ≤ y₂) :
    let Δ := r₂ - r₁
    let δ := y₂ - y₁
    let ξ₁ := s₀ - r₁ - A / y₁
    let ξ₂ := s₀ - r₂ - A / y₂
    let v₁ := max ξ₁ 0
    barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
      - barrierUr s₀ β A r₁ y₁ * Δ - barrierUy s₀ β A r₁ y₁ * δ
      - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * δ ^ 2 =
    ((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
      (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2) -
    3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3 -
    3 * β * v₁ * Δ ^ 2 +
    6 * β * v₁ * (A / (y₁ * y₂)) * (Δ * δ) +
    3 * β * v₁ * ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * δ ^ 3 := by
  intro Δ δ ξ₁ ξ₂ v₁
  have hy1_ne : y₁ ≠ 0 := (lt_of_lt_of_le (div_pos hA (by positivity)) hy1).ne'
  have hy2_ne : y₂ ≠ 0 := (lt_of_lt_of_le (div_pos hA (by positivity)) hy2).ne'
  obtain ⟨hu1, hur1, huy1, huyy1⟩ := barrierU_of_ge_half hs₀ hA hr1 (hr12.trans hr2) hy1 (β := β)
  obtain ⟨hu2, -, -, -⟩ := barrierU_of_ge_half hs₀ hA (hr1.trans hr12) hr2 hy2 (β := β)
  rw [hu2, hu1, hur1, huy1, huyy1]
  have hd1 : ξ₂ - ξ₁ = -Δ + (A / (y₁ * y₂)) * δ := by
    simp only [ξ₁, ξ₂, Δ, δ]; field_simp [hy1_ne, hy2_ne]; ring
  have hlin : (ξ₂ - ξ₁) - (-Δ + (A / y₁ ^ 2) * δ - (A / y₁ ^ 3) * δ ^ 2) =
      (A / (y₁ ^ 3 * y₂)) * δ ^ 3 := by
    rw [hd1]
    simp only [δ]
    have hy12 : y₁ * y₂ ≠ 0 := mul_ne_zero hy1_ne hy2_ne
    field_simp [hy1_ne, hy2_ne, hy12]
    ring
  have hsq : (ξ₂ - ξ₁) ^ 2 - (A / y₁ ^ 2) ^ 2 * δ ^ 2 =
      Δ ^ 2 - 2 * (A / (y₁ * y₂)) * (Δ * δ) -
        ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * δ ^ 3 := by
    rw [hd1]
    simp only [δ]
    have hy12 : y₁ * y₂ ≠ 0 := mul_ne_zero hy1_ne hy2_ne
    field_simp [hy1_ne, hy2_ne, hy12]
    ring
  change -β * (max ξ₂ 0) ^ 3 - -β * v₁ ^ 3 - 3 * β * v₁ ^ 2 * Δ -
      -3 * β * v₁ ^ 2 * (A / y₁ ^ 2) * δ -
      1 / 2 * (-6 * β * v₁ * (A / y₁ ^ 2) ^ 2 + 6 * β * v₁ ^ 2 * (A / y₁ ^ 3)) * δ ^ 2 = _
  linear_combination -3 * β * v₁ ^ 2 * hlin - 3 * β * v₁ * hsq

/-- Regime 1 (`y₁, y₂ ≥ A / (2 s₀)`): explicit `K₁`, zero `nlinarith`! -/
private lemma barrierU_taylor_regime1 {s₀ β A r₁ r₂ y₁ y₂ : ℝ}
    (hs₀ : 0 < s₀) (hβ : 0 < β) (hA : 0 < A)
    (hr1 : 0 ≤ r₁) (hr12 : r₁ ≤ r₂) (hr2 : r₂ ≤ s₀)
    (hy1 : A / (2 * s₀) ≤ y₁) (hy2 : A / (2 * s₀) ≤ y₂) :
    let M := 4 * s₀ ^ 2 / A
    let q := 2 * s₀ / A
    let K₁ := max (4 * β * s₀ + 3 * β * s₀)
      (max (6 * β * s₀ * M)
        (4 * β * M ^ 3 + 3 * β * s₀ ^ 2 * q ^ 2 * M + 6 * β * s₀ * q * M ^ 2))
    |barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
      - barrierUr s₀ β A r₁ y₁ * (r₂ - r₁)
      - barrierUy s₀ β A r₁ y₁ * (y₂ - y₁)
      - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * (y₂ - y₁) ^ 2| ≤
    K₁ * ((r₂ - r₁) ^ 2 + (r₂ - r₁) * |y₂ - y₁| + |y₂ - y₁| ^ 3) := by
  intro M q K₁
  set Δ := r₂ - r₁
  set δ := y₂ - y₁
  set ξ₁ := s₀ - r₁ - A / y₁
  set ξ₂ := s₀ - r₂ - A / y₂
  set v₁ := max ξ₁ 0
  have hΔ0 : 0 ≤ Δ := sub_nonneg.mpr hr12
  have hΔs : Δ ≤ s₀ := by linarith
  have hM0 : 0 < M := by positivity
  have hq0 : 0 < q := by positivity
  have hy1_pos : 0 < y₁ := lt_of_lt_of_le (div_pos hA (by positivity)) hy1
  have hy2_pos : 0 < y₂ := lt_of_lt_of_le (div_pos hA (by positivity)) hy2
  have hv1_0 : 0 ≤ v₁ := le_max_right _ _
  have hv1_le : v₁ ≤ s₀ := max_le (by have := div_pos hA hy1_pos; linarith) hs₀.le
  have hinv1 : 1 / y₁ ≤ q := by
    rw [div_le_div_iff₀ hy1_pos hA]; have := (div_le_iff₀ (by positivity)).mp hy1; linarith
  have hinv2 : 1 / y₂ ≤ q := by
    rw [div_le_div_iff₀ hy2_pos hA]; have := (div_le_iff₀ (by positivity)).mp hy2; linarith
  have hAy1_2 : A / y₁ ^ 2 ≤ M := by
    have : A / y₁ ^ 2 = A * (1 / y₁) ^ 2 := by ring
    rw [this]; calc A * (1 / y₁) ^ 2 ≤ A * q ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv1 2) hA.le
      _ = M := by simp only [M, q]; field_simp; ring
  have hAy12 : A / (y₁ * y₂) ≤ M := by
    have : A / (y₁ * y₂) = A * ((1 / y₁) * (1 / y₂)) := by ring
    rw [this]; calc A * ((1 / y₁) * (1 / y₂)) ≤ A * (q * q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hinv1 hinv2 (by positivity) hq0.le) hA.le
      _ = M := by simp only [M, q]; field_simp; ring
  have hAy122 : A / (y₁ ^ 2 * y₂) ≤ q * M := by
    calc A / (y₁ ^ 2 * y₂) = (1 / y₂) * (A / y₁ ^ 2) := by ring
      _ ≤ q * M := mul_le_mul hinv2 hAy1_2 (by positivity) hq0.le
  have hAy132 : A / (y₁ ^ 3 * y₂) ≤ q ^ 2 * M := by
    calc A / (y₁ ^ 3 * y₂) = (1 / y₁) * (A / (y₁ ^ 2 * y₂)) := by ring
      _ ≤ q * (q * M) := mul_le_mul hinv1 hAy122 (by positivity) hq0.le
      _ = q ^ 2 * M := by ring
  -- Bound each of the 5 terms in `barrierU_taylor_split`
  have hdξ_abs : |ξ₂ - ξ₁| ≤ Δ + M * |δ| := by
    have hd1 : ξ₂ - ξ₁ = -Δ + (A / (y₁ * y₂)) * δ := by
      simp only [ξ₁, ξ₂, Δ, δ]; field_simp [hy1_pos.ne', hy2_pos.ne']; ring
    rw [hd1]
    calc |-Δ + (A / (y₁ * y₂)) * δ| ≤ |-Δ| + |(A / (y₁ * y₂)) * δ| := abs_add_le _ _
      _ = Δ + (A / (y₁ * y₂)) * |δ| := by
          rw [abs_neg, abs_of_nonneg hΔ0, abs_mul, abs_of_pos (div_pos hA (mul_pos hy1_pos hy2_pos))]
      _ ≤ Δ + M * |δ| := by gcongr
  have hT1 : |(-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
      (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2| ≤
      (4 * β * s₀) * Δ ^ 2 + (4 * β * M ^ 3) * |δ| ^ 3 := by
    refine (eta_cube_taylor hβ ξ₁ ξ₂).trans ?_
    have h3 := (pow_le_pow_left₀ (abs_nonneg _) hdξ_abs 3).trans
      (add_cube_le_four hΔ0 (mul_nonneg hM0.le (abs_nonneg δ)))
    have hΔ3 : Δ ^ 3 ≤ s₀ * Δ ^ 2 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right hΔs (sq_nonneg Δ)
    have h4 : 4 * Δ ^ 3 + 4 * (M * |δ|) ^ 3 ≤ (4 * s₀) * Δ ^ 2 + (4 * M ^ 3) * |δ| ^ 3 := by
      rw [mul_pow]; linarith
    calc β * |ξ₂ - ξ₁| ^ 3 ≤ β * ((4 * s₀) * Δ ^ 2 + (4 * M ^ 3) * |δ| ^ 3) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hβ.le
      _ = (4 * β * s₀) * Δ ^ 2 + (4 * β * M ^ 3) * |δ| ^ 3 := by ring
  have hT2 : |3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3| ≤
      (3 * β * s₀ ^ 2 * q ^ 2 * M) * |δ| ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hβ,
      abs_of_nonneg (sq_nonneg v₁), abs_of_pos (by positivity), abs_pow]
    have hv2 : v₁ ^ 2 ≤ s₀ ^ 2 := pow_le_pow_left₀ hv1_0 hv1_le 2
    calc 3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * |δ| ^ 3
        ≤ 3 * β * s₀ ^ 2 * (q ^ 2 * M) * |δ| ^ 3 := by gcongr
      _ = _ := by ring
  have hT3 : |3 * β * v₁ * Δ ^ 2| ≤ (3 * β * s₀) * Δ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hβ,
      abs_of_nonneg hv1_0, abs_of_nonneg (sq_nonneg Δ)]
    gcongr
  have hT4 : |6 * β * v₁ * (A / (y₁ * y₂)) * (Δ * δ)| ≤ (6 * β * s₀ * M) * (Δ * |δ|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_of_pos hβ, abs_of_nonneg hv1_0, abs_of_pos (by positivity), abs_of_nonneg hΔ0]
    gcongr
  have hT5 : |3 * β * v₁ * ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * δ ^ 3| ≤
      (6 * β * s₀ * q * M ^ 2) * |δ| ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hβ,
      abs_of_nonneg hv1_0, abs_of_pos (by positivity), abs_pow]
    have hsumM : A / y₁ ^ 2 + A / (y₁ * y₂) ≤ 2 * M := by linarith
    calc 3 * β * v₁ * ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * |δ| ^ 3
        ≤ 3 * β * s₀ * ((q * M) * (2 * M)) * |δ| ^ 3 := by gcongr
      _ = (6 * β * s₀ * q * M ^ 2) * |δ| ^ 3 := by ring
  -- Combine via triangle inequality and `K₁` definition (pure `linarith`!)
  rw [barrierU_taylor_split hs₀ hA hr1 hr12 hr2 hy1 hy2]
  have htri : |((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
        (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2) -
      3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3 - 3 * β * v₁ * Δ ^ 2 +
      6 * β * v₁ * (A / (y₁ * y₂)) * (Δ * δ) +
      3 * β * v₁ * ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * δ ^ 3| ≤
      (4 * β * s₀ + 3 * β * s₀) * Δ ^ 2 + (6 * β * s₀ * M) * (Δ * |δ|) +
      (4 * β * M ^ 3 + 3 * β * s₀ ^ 2 * q ^ 2 * M + 6 * β * s₀ * q * M ^ 2) * |δ| ^ 3 := by
    have h1 := abs_add_le (((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
        (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2) -
      3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3 - 3 * β * v₁ * Δ ^ 2 +
      6 * β * v₁ * (A / (y₁ * y₂)) * (Δ * δ))
      (3 * β * v₁ * ((A / (y₁ ^ 2 * y₂)) * (A / y₁ ^ 2 + A / (y₁ * y₂))) * δ ^ 3)
    have h2 := abs_add_le (((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
        (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2) -
      3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3 - 3 * β * v₁ * Δ ^ 2)
      (6 * β * v₁ * (A / (y₁ * y₂)) * (Δ * δ))
    have h3 := abs_sub (((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
        (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2) -
      3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3) (3 * β * v₁ * Δ ^ 2)
    have h4 := abs_sub ((-β * (max ξ₂ 0) ^ 3) - (-β * v₁ ^ 3) - (-3 * β * v₁ ^ 2) * (ξ₂ - ξ₁) -
        (1 / 2 : ℝ) * (-6 * β * v₁) * (ξ₂ - ξ₁) ^ 2)
      (3 * β * v₁ ^ 2 * (A / (y₁ ^ 3 * y₂)) * δ ^ 3)
    linarith
  have hK1_a : (4 * β * s₀ + 3 * β * s₀) * Δ ^ 2 ≤ K₁ * Δ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg Δ)
  have hK1_b : (6 * β * s₀ * M) * (Δ * |δ|) ≤ K₁ * (Δ * |δ|) :=
    mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (mul_nonneg hΔ0 (abs_nonneg δ))
  have hK1_c : (4 * β * M ^ 3 + 3 * β * s₀ ^ 2 * q ^ 2 * M + 6 * β * s₀ * q * M ^ 2) * |δ| ^ 3 ≤ K₁ * |δ| ^ 3 :=
    mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (pow_nonneg (abs_nonneg δ) 3)
  linarith

/-- Regime 2 (`¬ (y₁, y₂ ≥ A / (2 s₀))`): explicit `K₂`, zero `nlinarith`! -/
private lemma barrierU_taylor_regime2 {s₀ β A r₁ r₂ y₁ y₂ : ℝ}
    (hs₀ : 0 < s₀) (hβ : 0 < β) (hA : 0 < A)
    (hr1 : 0 ≤ r₁) (hr12 : r₁ ≤ r₂) (hr2 : r₂ ≤ s₀)
    (hbad : ¬ (A / (2 * s₀) ≤ y₁ ∧ A / (2 * s₀) ≤ y₂)) :
    let q := 2 * s₀ / A
    let K₂ := max (3 * β * s₀ ^ 2 * q)
      (2 * β * s₀ ^ 3 * q ^ 3 + (3 * β * s₀ ^ 4 / A) * q ^ 2 + (6 * β * s₀ ^ 5 / A ^ 2) * q)
    |barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
      - barrierUr s₀ β A r₁ y₁ * (r₂ - r₁)
      - barrierUy s₀ β A r₁ y₁ * (y₂ - y₁)
      - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * (y₂ - y₁) ^ 2| ≤
    K₂ * ((r₂ - r₁) ^ 2 + (r₂ - r₁) * |y₂ - y₁| + |y₂ - y₁| ^ 3) := by
  intro q K₂
  set Δ := r₂ - r₁
  set δ := y₂ - y₁
  have hΔ0 : 0 ≤ Δ := sub_nonneg.mpr hr12
  have hK2_0 : 0 ≤ K₂ := le_trans (by positivity) (le_max_left _ _)
  by_cases hboth : y₁ ≤ A / s₀ ∧ y₂ ≤ A / s₀
  · simp only [barrierU, barrierUr, barrierUy, barrierUyy,
      not_lt.mpr hboth.1, not_lt.mpr hboth.2, false_and, ite_false,
      zero_mul, sub_zero, mul_zero, abs_zero]
    positivity
  · have hhalf : A / (2 * s₀) < A / s₀ :=
      div_lt_div_of_pos_left hA hs₀ (lt_mul_of_one_lt_left hs₀ one_lt_two)
    have hgap : A / s₀ - A / (2 * s₀) = A / (2 * s₀) := by field_simp; norm_num
    have hδ_ge : A / (2 * s₀) ≤ |δ| := by
      rw [not_and_or, not_le, not_le] at hbad hboth
      rcases hbad with h1 | h2 <;> rcases hboth with h3 | h4
      · linarith [hhalf]
      · have hpos : 0 < δ := by simp only [δ]; linarith [hhalf]
        rw [abs_of_pos hpos]
        simp only [δ]
        linarith [hgap, hhalf]
      · have hneg : δ < 0 := by simp only [δ]; linarith [hhalf]
        rw [abs_of_neg hneg]
        simp only [δ]
        linarith [hgap, hhalf]
      · linarith [hhalf]
    have hinv : 1 ≤ q * |δ| := by
      have h1 := mul_le_mul_of_nonneg_left hδ_ge (by positivity : 0 ≤ q)
      have hc : q * (A / (2 * s₀)) = 1 := by simp only [q]; field_simp
      linarith
    have h1_2 : 1 ≤ q ^ 2 * |δ| ^ 2 := by simpa [mul_pow] using pow_le_pow_left₀ zero_le_one hinv 2
    have h1_3 : 1 ≤ q ^ 3 * |δ| ^ 3 := by simpa [mul_pow] using pow_le_pow_left₀ zero_le_one hinv 3
    -- Global bounds on `barrierU`, `barrierUr`, `barrierUy`, `barrierUyy`
    have hu_bd : ∀ r y, 0 ≤ r → r ≤ s₀ → |barrierU s₀ β A r y| ≤ β * s₀ ^ 3 := fun r y hr0 hrs => by
      unfold barrierU; split_ifs with h
      · have hy := lt_trans (div_pos hA hs₀) h.1
        have hv0 := sub_pos.mpr h.2
        have hvs : s₀ - r - A / y ≤ s₀ := by have := div_pos hA hy; linarith
        rw [abs_mul, abs_neg, abs_of_pos hβ, abs_of_nonneg (pow_nonneg hv0.le 3)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0.le hvs 3) hβ.le
      · rw [abs_zero]; positivity
    have hur_bd : |barrierUr s₀ β A r₁ y₁| ≤ 3 * β * s₀ ^ 2 := by
      unfold barrierUr; split_ifs with h
      · have hy := lt_trans (div_pos hA hs₀) h.1
        have hv0 := sub_pos.mpr h.2
        have hvs : s₀ - r₁ - A / y₁ ≤ s₀ := by have := div_pos hA hy; linarith
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0.le hvs 2) (by positivity)
      · rw [abs_zero]; positivity
    have huy_bd : |barrierUy s₀ β A r₁ y₁| ≤ 3 * β * s₀ ^ 4 / A := by
      unfold barrierUy; split_ifs with h
      · have hy := lt_trans (div_pos hA hs₀) h.1
        have hv0 := sub_pos.mpr h.2
        have hvs : s₀ - r₁ - A / y₁ ≤ s₀ := by have := div_pos hA hy; linarith
        have hAy : A / y₁ ^ 2 ≤ s₀ ^ 2 / A := by
          rw [div_le_div_iff₀ (pow_pos hy 2) hA]
          have hlt := (div_lt_iff₀ hs₀).mp h.1
          have hsq := pow_le_pow_left₀ hA.le hlt.le 2; rw [mul_pow] at hsq
          have : A ^ 2 * A ≤ y₁ ^ 2 * s₀ ^ 2 * A := mul_le_mul_of_nonneg_right hsq hA.le
          linarith [show A * A = A ^ 2 by ring, show s₀ ^ 2 * y₁ ^ 2 = y₁ ^ 2 * s₀ ^ 2 by ring,
            show A * A * A = A ^ 2 * A by ring]
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3),
          abs_of_pos hβ, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
        calc 3 * β * (s₀ - r₁ - A / y₁) ^ 2 * (A / y₁ ^ 2)
            ≤ 3 * β * s₀ ^ 2 * (s₀ ^ 2 / A) := by gcongr
          _ = 3 * β * s₀ ^ 4 / A := by ring
      · rw [abs_zero]; positivity
    have huyy_bd : |barrierUyy s₀ β A r₁ y₁| ≤ 12 * β * s₀ ^ 5 / A ^ 2 := by
      unfold barrierUyy; split_ifs with h
      · have hy := lt_trans (div_pos hA hs₀) h.1
        have hv0 := sub_pos.mpr h.2
        have hvs : s₀ - r₁ - A / y₁ ≤ s₀ := by have := div_pos hA hy; linarith
        have hlt := (div_lt_iff₀ hs₀).mp h.1
        have hAy2 : A / y₁ ^ 2 ≤ s₀ ^ 2 / A := by
          have h1 : 1 / y₁ ≤ s₀ / A := by rw [div_le_div_iff₀ hy hA]; linarith
          calc A / y₁ ^ 2 = A * (1 / y₁) ^ 2 := by ring
            _ ≤ A * (s₀ / A) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 2) hA.le
            _ = s₀ ^ 2 / A := by field_simp
        have hAy3 : A / y₁ ^ 3 ≤ s₀ ^ 3 / A ^ 2 := by
          have h1 : 1 / y₁ ≤ s₀ / A := by rw [div_le_div_iff₀ hy hA]; linarith
          calc A / y₁ ^ 3 = A * (1 / y₁) ^ 3 := by ring
            _ ≤ A * (s₀ / A) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 3) hA.le
            _ = s₀ ^ 3 / A ^ 2 := by field_simp
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 6),
          abs_of_pos hβ, abs_of_nonneg hv0.le, abs_of_nonneg (sq_nonneg _),
          abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos hβ,
          abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
        calc 6 * β * (s₀ - r₁ - A / y₁) * (A / y₁ ^ 2) ^ 2 +
              6 * β * (s₀ - r₁ - A / y₁) ^ 2 * (A / y₁ ^ 3)
            ≤ 6 * β * s₀ * (s₀ ^ 2 / A) ^ 2 + 6 * β * s₀ ^ 2 * (s₀ ^ 3 / A ^ 2) := by gcongr
          _ = 12 * β * s₀ ^ 5 / A ^ 2 := by ring
      · rw [abs_zero]; positivity
    have htri : |barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
        - barrierUr s₀ β A r₁ y₁ * Δ - barrierUy s₀ β A r₁ y₁ * δ
        - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * δ ^ 2| ≤
        |barrierU s₀ β A r₂ y₂| + |barrierU s₀ β A r₁ y₁| +
        |barrierUr s₀ β A r₁ y₁| * Δ + |barrierUy s₀ β A r₁ y₁| * |δ| +
        (1 / 2 : ℝ) * |barrierUyy s₀ β A r₁ y₁| * |δ| ^ 2 := by
      have e1 : |barrierUr s₀ β A r₁ y₁ * Δ| = |barrierUr s₀ β A r₁ y₁| * Δ := by
        rw [abs_mul, abs_of_nonneg hΔ0]
      have e2 : |barrierUy s₀ β A r₁ y₁ * δ| = |barrierUy s₀ β A r₁ y₁| * |δ| := abs_mul _ _
      have e3 : |(1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * δ ^ 2| =
          (1 / 2 : ℝ) * |barrierUyy s₀ β A r₁ y₁| * |δ| ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow]
      linarith [abs_sub (barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁ - barrierUr s₀ β A r₁ y₁ * Δ -
          barrierUy s₀ β A r₁ y₁ * δ) ((1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * δ ^ 2),
        abs_sub (barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁ - barrierUr s₀ β A r₁ y₁ * Δ)
          (barrierUy s₀ β A r₁ y₁ * δ),
        abs_sub (barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁) (barrierUr s₀ β A r₁ y₁ * Δ),
        abs_sub (barrierU s₀ β A r₂ y₂) (barrierU s₀ β A r₁ y₁)]
    have hB1 : |barrierU s₀ β A r₂ y₂| + |barrierU s₀ β A r₁ y₁| ≤ (2 * β * s₀ ^ 3 * q ^ 3) * |δ| ^ 3 := by
      have := add_le_add (hu_bd r₂ y₂ (hr1.trans hr12) hr2) (hu_bd r₁ y₁ hr1 (hr12.trans hr2))
      calc _ ≤ 2 * β * s₀ ^ 3 := by linarith
        _ ≤ (2 * β * s₀ ^ 3) * (q ^ 3 * |δ| ^ 3) := le_mul_of_one_le_right (by positivity) h1_3
        _ = _ := by ring
    have hB2 : |barrierUr s₀ β A r₁ y₁| * Δ ≤ (3 * β * s₀ ^ 2 * q) * (Δ * |δ|) := by
      calc _ ≤ (3 * β * s₀ ^ 2) * Δ := mul_le_mul_of_nonneg_right hur_bd hΔ0
        _ ≤ ((3 * β * s₀ ^ 2) * Δ) * (q * |δ|) := le_mul_of_one_le_right (by positivity) hinv
        _ = _ := by ring
    have hB3 : |barrierUy s₀ β A r₁ y₁| * |δ| ≤ ((3 * β * s₀ ^ 4 / A) * q ^ 2) * |δ| ^ 3 := by
      calc _ ≤ (3 * β * s₀ ^ 4 / A) * |δ| := mul_le_mul_of_nonneg_right huy_bd (abs_nonneg δ)
        _ ≤ ((3 * β * s₀ ^ 4 / A) * |δ|) * (q ^ 2 * |δ| ^ 2) := le_mul_of_one_le_right (by positivity) h1_2
        _ = _ := by ring
    have hB4 : (1 / 2 : ℝ) * |barrierUyy s₀ β A r₁ y₁| * |δ| ^ 2 ≤
        ((6 * β * s₀ ^ 5 / A ^ 2) * q) * |δ| ^ 3 := by
      calc _ ≤ (1 / 2 : ℝ) * (12 * β * s₀ ^ 5 / A ^ 2) * |δ| ^ 2 := by gcongr
        _ = (6 * β * s₀ ^ 5 / A ^ 2) * |δ| ^ 2 := by ring
        _ ≤ ((6 * β * s₀ ^ 5 / A ^ 2) * |δ| ^ 2) * (q * |δ|) := le_mul_of_one_le_right (by positivity) hinv
        _ = _ := by ring
    have hK2_b : (3 * β * s₀ ^ 2 * q) * (Δ * |δ|) ≤ K₂ * (Δ * |δ|) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hΔ0 (abs_nonneg δ))
    have hK2_c : (2 * β * s₀ ^ 3 * q ^ 3 + (3 * β * s₀ ^ 4 / A) * q ^ 2 + (6 * β * s₀ ^ 5 / A ^ 2) * q) * |δ| ^ 3 ≤
        K₂ * |δ| ^ 3 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (abs_nonneg δ) 3)
    have hK2_a : 0 ≤ K₂ * Δ ^ 2 := mul_nonneg hK2_0 (sq_nonneg Δ)
    linarith

/-- Combined 2nd-order Taylor bound for `barrierU` on `[0, s₀] × ℝ` (8 lines!). -/
private lemma barrierU_taylor_rem {s₀ β A : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r₁ r₂ y₁ y₂ : ℝ,
      0 ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ s₀ →
      |barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
        - barrierUr s₀ β A r₁ y₁ * (r₂ - r₁)
        - barrierUy s₀ β A r₁ y₁ * (y₂ - y₁)
        - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * (y₂ - y₁) ^ 2| ≤
      K * ((r₂ - r₁) ^ 2 + (r₂ - r₁) * |y₂ - y₁| + |y₂ - y₁| ^ 3) := by
  set M := 4 * s₀ ^ 2 / A
  set q := 2 * s₀ / A
  set K₁ := max (4 * β * s₀ + 3 * β * s₀)
    (max (6 * β * s₀ * M) (4 * β * M ^ 3 + 3 * β * s₀ ^ 2 * q ^ 2 * M + 6 * β * s₀ * q * M ^ 2))
  set K₂ := max (3 * β * s₀ ^ 2 * q)
    (2 * β * s₀ ^ 3 * q ^ 3 + (3 * β * s₀ ^ 4 / A) * q ^ 2 + (6 * β * s₀ ^ 5 / A ^ 2) * q)
  refine ⟨max K₁ K₂, le_trans (le_trans (by positivity) (le_max_left _ _)) (le_max_left K₁ K₂),
    fun r₁ r₂ y₁ y₂ hr1 hr12 hr2 => ?_⟩
  have hnn : 0 ≤ (r₂ - r₁) ^ 2 + (r₂ - r₁) * |y₂ - y₁| + |y₂ - y₁| ^ 3 :=
    add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hr12) (abs_nonneg _)))
      (pow_nonneg (abs_nonneg _) 3)
  by_cases hgood : A / (2 * s₀) ≤ y₁ ∧ A / (2 * s₀) ≤ y₂
  · exact (barrierU_taylor_regime1 hs₀ hβ hA hr1 hr12 hr2 hgood.1 hgood.2).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) hnn)
  · exact (barrierU_taylor_regime2 hs₀ hβ hA hr1 hr12 hr2 hgood).trans
      (mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) hnn)

/-! ### Part 3: Discrete Doléans product = 1 -/

private lemma lintegral_discrete_doleans_eq_one {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (N : ℕ) (hN : 0 < N)
    (c : ℕ → Ω → ℝ)
    (hc : ∀ k < N, Measurable[(pathFiltration B).σAlg ((k : ℝ) * (s₀ / (N : ℝ)))] (c k)) :
    ∀ m ≤ N,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range m,
        (c k ω * wnnIncr B ⟨0, hd⟩ ((k : ℝ) * (s₀ / (N : ℝ))) (((k + 1 : ℕ) : ℝ) * (s₀ / (N : ℝ))) ω -
          (1 / 2 : ℝ) * c k ω ^ 2 * (s₀ / (N : ℝ))))) ∂P = 1 := by
  set Δ : ℝ := s₀ / (N : ℝ)
  have hΔ0 : 0 ≤ Δ := div_nonneg hs₀ (Nat.cast_nonneg N)
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hmN : m < N := Nat.lt_of_succ_le hm
    set t_m : ℝ := (m : ℝ) * Δ
    set t_m1 : ℝ := ((m + 1 : ℕ) : ℝ) * Δ
    have htm0 : 0 ≤ t_m := by positivity
    have hstep : t_m ≤ t_m1 := by simp only [t_m, t_m1]; push_cast; nlinarith
    have hdiff : t_m1 - t_m = Δ := by simp only [t_m, t_m1]; push_cast; ring
    set A_m : Ω → ℝ := fun ω => Real.exp (∑ k ∈ Finset.range m,
      (c k ω * wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k + 1 : ℕ) : ℝ) * Δ) ω -
        (1 / 2 : ℝ) * c k ω ^ 2 * Δ))
    have hAm_meas : Measurable[(pathFiltration B).σAlg t_m] A_m := by
      refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun k hk => ?_)
      have hkm : k < m := Finset.mem_range.mp hk
      have htk_le : (k : ℝ) * Δ ≤ t_m := by
        simp only [t_m]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm.le) hΔ0
      have htk1_le : ((k + 1 : ℕ) : ℝ) * Δ ≤ t_m := by
        simp only [t_m]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) hΔ0
      exact (((hc k (hkm.trans hmN)).mono ((pathFiltration B).mono htk_le) le_rfl).mul
        (measurable_wnnIncr_pathFiltration B ⟨0, hd⟩ (by positivity) (by positivity)
          htk_le htk1_le)).sub
        (((((hc k (hkm.trans hmN)).mono ((pathFiltration B).mono htk_le) le_rfl).pow_const 2).const_mul _).mul_const _)
    have hpair_indep : IndepFun (fun ω => (A_m ω, c m ω))
        (fun ω => wnnIncr B ⟨0, hd⟩ t_m t_m1 ω) P :=
      indepFun_pathFiltration_wnnIncr B ⟨0, hd⟩ hstep (hAm_meas.prodMk (hc m hmN))
    have hlaw_inc := hasLaw_wnnIncr B ⟨0, hd⟩ htm0 hstep
    let F : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (q.1.1 * Real.exp (q.1.2 * q.2 - (1 / 2 : ℝ) * q.1.2 ^ 2 * Δ))
    have hsplit : (fun ω => ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range (m + 1),
        (c k ω * wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k + 1 : ℕ) : ℝ) * Δ) ω -
          (1 / 2 : ℝ) * c k ω ^ 2 * Δ)))) =
        fun ω => F ((A_m ω, c m ω), wnnIncr B ⟨0, hd⟩ t_m t_m1 ω) := by
      funext ω; simp only [F, Finset.sum_range_succ, Real.exp_add, A_m, t_m, t_m1]
    rw [hsplit]
    have hpair_amb : Measurable (fun ω => (A_m ω, c m ω)) :=
      (hAm_meas.mono ((pathFiltration B).le_ambient _) le_rfl).prodMk
        ((hc m hmN).mono ((pathFiltration B).le_ambient _) le_rfl)
    have hprod_map : P.map (fun ω => ((A_m ω, c m ω), wnnIncr B ⟨0, hd⟩ t_m t_m1 ω)) =
        (P.map (fun ω => (A_m ω, c m ω))).prod (gaussianReal 0 (Real.toNNReal Δ)) := by
      rw [← hdiff, ← hlaw_inc.map_eq]
      exact (indepFun_iff_map_prod_eq_prod_map_map hpair_amb.aemeasurable
        (measurable_wnnIncr B ⟨0, hd⟩ t_m t_m1).aemeasurable).mp hpair_indep
    have hF_meas : Measurable F := by unfold F; fun_prop
    rw [← lintegral_map hF_meas (hpair_amb.prodMk (measurable_wnnIncr B ⟨0, hd⟩ t_m t_m1)),
      hprod_map, lintegral_prod _ hF_meas.aemeasurable]
    have hinner : ∀ p : ℝ × ℝ, 0 ≤ p.1 →
        ∫⁻ z : ℝ, F (p, z) ∂(gaussianReal 0 (Real.toNNReal Δ)) = ENNReal.ofReal p.1 := by
      intro p hp
      have hfactor : ∀ z : ℝ, F (p, z) =
          ENNReal.ofReal p.1 * ENNReal.ofReal (Real.exp (p.2 * z - (1 / 2 : ℝ) * p.2 ^ 2 * Δ)) :=
        fun z => ENNReal.ofReal_mul hp
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (by fun_prop)]
      have hmgf : ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (p.2 * z - (1 / 2 : ℝ) * p.2 ^ 2 * Δ))
          ∂(gaussianReal 0 (Real.toNNReal Δ)) = 1 := by
        have hint : Integrable (fun z : ℝ => Real.exp (p.2 * z - (1 / 2 : ℝ) * p.2 ^ 2 * Δ))
            (gaussianReal 0 (Real.toNNReal Δ)) := by
          simpa [sub_eq_add_neg, Real.exp_add] using
            (ProbabilityTheory.integrable_exp_mul_gaussianReal p.2).mul_const
              (Real.exp (-((1 / 2 : ℝ) * p.2 ^ 2 * Δ)))
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        have hval : ∫ z : ℝ, Real.exp (p.2 * z - (1 / 2 : ℝ) * p.2 ^ 2 * Δ)
            ∂(gaussianReal 0 (Real.toNNReal Δ)) = 1 := by
          simp_rw [sub_eq_add_neg, Real.exp_add]
          rw [integral_mul_const]
          have hmgf_def : ∫ z : ℝ, Real.exp (p.2 * z) ∂(gaussianReal 0 (Real.toNNReal Δ)) =
              mgf id (gaussianReal 0 (Real.toNNReal Δ)) p.2 := rfl
          rw [hmgf_def, mgf_id_gaussianReal, Real.coe_toNNReal _ hΔ0, ← Real.exp_add]
          have hexp0 : 0 * p.2 + Δ * p.2 ^ 2 / 2 + -((1 / 2 : ℝ) * p.2 ^ 2 * Δ) = 0 := by ring
          rw [hexp0, Real.exp_zero]
        rw [hval, ENNReal.ofReal_one]
      rw [hmgf, mul_one]
    have hae_pos : ∀ᵐ p : ℝ × ℝ ∂(P.map (fun ω => (A_m ω, c m ω))), 0 ≤ p.1 := by
      rw [ae_map_iff hpair_amb.aemeasurable (measurableSet_le measurable_const measurable_fst)]
      exact ae_of_all _ fun ω => (Real.exp_pos _).le
    rw [lintegral_congr_ae (hae_pos.mono fun p hp => hinner p hp),
      show ∫⁻ a : ℝ × ℝ, ENNReal.ofReal a.1 ∂(P.map (fun ω => (A_m ω, c m ω))) =
        ∫⁻ a : ℝ × ℝ, (ENNReal.ofReal ∘ Prod.fst) a ∂(P.map (fun ω => (A_m ω, c m ω))) from rfl,
      lintegral_map (ENNReal.measurable_ofReal.comp measurable_fst) hpair_amb]
    exact ih (Nat.le_of_succ_le hm)

/-! ### Part 4: Dyadic subinterval QV & weighted QV (clean `2^(m+n)` and `cellProd` rewrites) -/

private lemma sum_range_mul_eq_sum_Ico {α : Type*} [AddCommMonoid α] (a b : ℕ) (f : ℕ → α) :
    ∑ k ∈ Finset.range (a * b), f k =
      ∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico (j * b) ((j + 1) * b), f k := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, Nat.succ_mul, Nat.add_sub_cancel_left]

omit [IsProbabilityMeasure P] in
private lemma ae_tendsto_zero_of_summable_integral_sq {A : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (fun ω => A n ω ^ 2) P)
    {b : ℕ → ℝ} (hb : Summable b) (hle : ∀ n, ∫ ω, A n ω ^ 2 ∂P ≤ b n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 0) := by
  have hmeas2 : ∀ n, Measurable fun ω => ENNReal.ofReal (A n ω ^ 2) := fun n =>
    ((hmeas n).pow_const 2).ennreal_ofReal
  have h1 : ∫⁻ ω, ∑' n, ENNReal.ofReal (A n ω ^ 2) ∂P ≠ ∞ := by
    rw [lintegral_tsum fun n => (hmeas2 n).aemeasurable]
    have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal (A n ω ^ 2) ∂P ≤ ENNReal.ofReal (b n) := fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ fun _ => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hle n)
    exact ne_top_of_le_ne_top hb.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hn)
  filter_upwards [ae_lt_top (Measurable.tsum hmeas2) h1] with ω hω
  have h3 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h4 : Tendsto (fun n => A n ω ^ 2) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
    simp only [Function.comp_def, ENNReal.toReal_zero] at h
    exact h.congr fun n => ENNReal.toReal_ofReal (sq_nonneg _)
  have h5 : Tendsto (fun n => Real.sqrt (A n ω ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h4
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr (h5.congr fun n => Real.sqrt_sq_eq_abs _)

private lemma ae_dyadic_subinterval_qv {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∀ᵐ ω ∂P, ∀ (m : ℕ), ∀ j < 2 ^ m,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) ω k -
           MultiBrownian.W B ((i : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) ω k) ^ 2)
        atTop (𝓝 (s₀ / ((2 ^ m : ℕ) : ℝ))) := by
  rw [ae_all_iff]; intro m
  rw [ae_all_iff]; intro j
  by_cases hj : j < 2 ^ m
  · set len : ℝ := s₀ / ((2 ^ m : ℕ) : ℝ)
    set a : ℝ := (j : ℝ) * len
    let τ (n i : ℕ) : ℝ := a + (i : ℝ) * (len / ((2 ^ n : ℕ) : ℝ))
    let A (n : ℕ) (ω : Ω) : ℝ :=
      ∑ i ∈ Finset.range (2 ^ n), (1 : ℝ) * cellProd B k k (τ n i) (τ n (i + 1)) ω
    have hsq := fun n => integral_sum_mul_cellProd_sq B k k (τ := τ n)
      (by simp only [τ, a, len]; positivity)
      (fun i₁ i₂ h12 => by
        dsimp only [τ]
        gcongr)
      (fun _ _ => (1 : ℝ)) (2 ^ n) (fun _ _ => measurable_const) (fun _ _ => memLp_const 1)
    have hae0 : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 0) := by
      refine ae_tendsto_zero_of_summable_integral_sq
        (fun n => Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_cellProd B k k _ _))
        (fun n => (hsq n).1)
        (b := fun n => ((gaussMoment 2 + 1) * len ^ 2) * (1 / 2 : ℝ) ^ n)
        ((summable_geometric_two).mul_left _) (fun n => ?_)
      rw [(hsq n).2]
      calc ∑ i ∈ Finset.range (2 ^ n), (∫ _ω, (1 : ℝ) ^ 2 ∂P) *
              ∫ ω, cellProd B k k (τ n i) (τ n (i + 1)) ω ^ 2 ∂P
          ≤ ∑ _i ∈ Finset.range (2 ^ n), (gaussMoment 2 + 1) * (len / ((2 ^ n : ℕ) : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul]
            have hstep : τ n (i + 1) - τ n i = len / ((2 ^ n : ℕ) : ℝ) := by simp only [τ]; push_cast; ring
            rw [← hstep]
            exact (integrable_cellProd_sq_and_le B k k (by simp only [τ, a, len]; positivity)
              (by linarith [show 0 ≤ len / ((2 ^ n : ℕ) : ℝ) by positivity])).2
        _ = ((gaussMoment 2 + 1) * len ^ 2) * (1 / 2 : ℝ) ^ n := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow, one_div_pow]
            push_cast; field_simp
    filter_upwards [hae0] with ω hω _
    have hshift : ∀ n,
        ∑ i ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) ω k -
           MultiBrownian.W B ((i : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) ω k) ^ 2 =
        A n ω + len := fun n => by
      have h2pow : ((2 ^ (m + n) : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ) := by
        rw [pow_add, Nat.cast_mul]
      have hτ_eq : ∀ r : ℕ, τ n r = ((j * 2 ^ n + r : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) := fun r => by
        simp only [τ, a, len, h2pow]; push_cast; field_simp
      have hstep : ∀ i : ℕ, τ n (i + 1) - τ n i = len / ((2 ^ n : ℕ) : ℝ) := fun i => by
        simp only [τ]; push_cast; ring
      have hsum_len : ∑ _i ∈ Finset.range (2 ^ n), (len / ((2 ^ n : ℕ) : ℝ)) = len := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
      rw [Finset.sum_Ico_eq_sum_range, Nat.succ_mul, Nat.add_sub_cancel_left, ← hsum_len,
        show A n ω + ∑ _i ∈ Finset.range (2 ^ n), (len / ((2 ^ n : ℕ) : ℝ)) =
          ∑ i ∈ Finset.range (2 ^ n), ((1 : ℝ) * cellProd B k k (τ n i) (τ n (i + 1)) ω +
            len / ((2 ^ n : ℕ) : ℝ)) from (Finset.sum_add_distrib).symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcell : (1 : ℝ) * cellProd B k k (τ n i) (τ n (i + 1)) ω + len / ((2 ^ n : ℕ) : ℝ) =
          (MultiBrownian.W B (τ n (i + 1)) ω k - MultiBrownian.W B (τ n i) ω k) ^ 2 := by
        simp only [cellProd, ite_true, one_mul, hstep i, sub_add_cancel, wnnIncr_eq_W, sq]
      rw [hcell, hτ_eq i, hτ_eq (i + 1), show j * 2 ^ n + (i + 1) = (j * 2 ^ n + i) + 1 by omega]
    have hT : Tendsto (fun n => A n ω + len) atTop (𝓝 len) := by
      simpa [zero_add] using hω.add_const len
    exact hT.congr fun n => (hshift n).symm
  · exact ae_of_all _ fun _ h => absurd h hj

private lemma tendsto_dyadic_weighted_qv_of_subintervals {s₀ : ℝ} (hs₀ : 0 < s₀)
    {w : ℝ → ℝ}
    (hqv : ∀ m : ℕ, ∀ j < 2 ^ m,
      Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2)
        atTop (𝓝 (s₀ / ((2 ^ m : ℕ) : ℝ))))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 s₀)) :
    Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range (2 ^ n),
        g ((k : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ))) *
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)))) ^ 2)
      atTop (𝓝 (∫ r in (0 : ℝ)..s₀, g r)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  obtain ⟨δ, hδ, hδ_bd⟩ := Metric.uniformContinuousOn_iff_le.mp huc (ε / (6 * (s₀ + 1))) (by positivity)
  have hriem := (tendsto_lebRiemann_of_continuousOn hs₀.le hg).comp
    (StrictMono.tendsto_atTop (fun a b hab => Nat.sub_lt_sub_right (Nat.one_le_two_pow)
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hab)))
  obtain ⟨m₁, hm₁⟩ := (Metric.tendsto_atTop.mp hriem) (ε / 3) (by positivity)
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt (s₀ / δ)
  set m : ℕ := max m₁ m₂
  have hblock : s₀ / ((2 ^ m : ℕ) : ℝ) ≤ δ := by
    have hlt : s₀ / δ < ((2 ^ m : ℕ) : ℝ) := lt_of_lt_of_le hm₂ (by
      exact_mod_cast (le_max_right m₁ m₂).trans (Nat.lt_two_pow_self (n := m)).le)
    rw [div_le_iff₀ (by positivity)]
    linarith [(div_lt_iff₀ hδ).mp hlt]
  have hsum_qv : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
        ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2)
      atTop (𝓝 (∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
        (s₀ / ((2 ^ m : ℕ) : ℝ)))) :=
    tendsto_finsetSum _ fun j hj => (hqv m j (Finset.mem_range.mp hj)).const_mul _
  have htot_qv : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range (2 ^ (m + n)),
        (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
         w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2) atTop (𝓝 s₀) := by
    have h := tendsto_finsetSum (Finset.range (2 ^ m)) fun j hj => hqv m j (Finset.mem_range.mp hj)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hs : ((2 ^ m : ℕ) : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) = s₀ := by field_simp
    rw [hs] at h
    exact h.congr fun n => by rw [pow_add, sum_range_mul_eq_sum_Ico]
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hsum_qv) (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp htot_qv) 1 one_pos
  refine ⟨m + max N₁ N₂, fun r hr => ?_⟩
  set n := r - m
  have hr_eq : r = m + n := by omega
  rw [hr_eq]
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have h2pow : ((2 ^ (m + n) : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ) := by
    rw [pow_add, Nat.cast_mul]
  have hqv_bd : ∑ k ∈ Finset.range (2 ^ (m + n)),
      (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
       w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2 ≤ s₀ + 1 := by
    have h := hN₂ n hn2; rw [Real.dist_eq, abs_lt] at h; linarith
  have herr1 : |∑ k ∈ Finset.range (2 ^ (m + n)),
        g ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) *
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2 -
      ∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
        ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2| ≤ ε / 3 := by
    have hrange : Finset.range (2 ^ (m + n)) = Finset.range (2 ^ m * 2 ^ n) := by rw [pow_add]
    rw [hrange, sum_range_mul_eq_sum_Ico, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j ∈ Finset.range (2 ^ m), ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          |g ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) - g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)))| *
            (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
             w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg
            (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
             w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))))]
      _ ≤ (ε / (6 * (s₀ + 1))) * ∑ k ∈ Finset.range (2 ^ (m + n)),
            (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
             w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2 := by
          have hrange' : Finset.range (2 ^ (m + n)) = Finset.range (2 ^ m * 2 ^ n) := by rw [pow_add]
          rw [hrange', sum_range_mul_eq_sum_Ico, Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hj' := Finset.mem_range.mp hj
          have hk' := Finset.mem_Ico.mp hk
          have heq : (j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) =
              ((j * 2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) := by
            rw [h2pow]; push_cast; field_simp
          have heq1 : ((j + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) =
              (((j + 1) * 2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) := by
            rw [h2pow]; push_cast; field_simp
          have hge : (j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) ≤ (k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) := by
            rw [heq]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk'.1) (by positivity)
          have hle1 : (k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) := by
            rw [heq1]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk'.2.le) (by positivity)
          have ht_dist : dist ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))
              ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) ≤ δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hge)]
            have hdiff : ((j + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) - (j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) =
                s₀ / ((2 ^ m : ℕ) : ℝ) := by push_cast; ring
            linarith
          have hk_le : k ≤ 2 ^ (m + n) := hk'.2.le.trans (by rw [pow_add]; exact Nat.mul_le_mul_right _ hj')
          exact hδ_bd _ ⟨by positivity, by
              calc (k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) ≤ ((2 ^ (m + n) : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)) :=
                    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk_le) (by positivity)
                _ = s₀ := by field_simp⟩
            _ ⟨by positivity, by
              calc (j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) ≤ ((2 ^ m : ℕ) : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ)) :=
                    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj'.le) (by positivity)
                _ = s₀ := by field_simp⟩ ht_dist
      _ ≤ (ε / (6 * (s₀ + 1))) * (s₀ + 1) := mul_le_mul_of_nonneg_left hqv_bd (by positivity)
      _ = ε / 6 := by field_simp
      _ ≤ ε / 3 := by linarith
  have herr2 := hN₁ n hn1
  have herr3 : dist (∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
        (s₀ / ((2 ^ m : ℕ) : ℝ))) (∫ r in (0 : ℝ)..s₀, g r) < ε / 3 := by
    have h := hm₁ m (le_max_left m₁ m₂)
    have h2m : (2 ^ m - 1 : ℕ) + 1 = 2 ^ m := Nat.sub_add_cancel Nat.one_le_two_pow
    simpa [Function.comp_def, h2m] using h
  rw [Real.dist_eq] at herr2 herr3 ⊢
  linarith [abs_sub_le (∑ k ∈ Finset.range (2 ^ (m + n)),
      g ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) *
        (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
         w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2)
    (∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
      ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
        (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
         w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2) (∫ r in (0 : ℝ)..s₀, g r),
    abs_sub_le (∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
      ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
        (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
         w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2)
    (∑ j ∈ Finset.range (2 ^ m), g ((j : ℝ) * (s₀ / ((2 ^ m : ℕ) : ℝ))) *
      (s₀ / ((2 ^ m : ℕ) : ℝ))) (∫ r in (0 : ℝ)..s₀, g r)]

/-! ### Part 5: Standalone pointwise limit of `logD n ω` (clean `sum_range_sub` + zero timeout!) -/

private lemma tendsto_logD_of_qv {s₀ β A x K : ℝ} (hs₀ : 0 < s₀) (_hβ : 0 < β) (hA : 0 < A)
    (hK0 : 0 ≤ K)
    (htay : ∀ r₁ r₂ y₁ y₂ : ℝ, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ s₀ →
      |barrierU s₀ β A r₂ y₂ - barrierU s₀ β A r₁ y₁
        - barrierUr s₀ β A r₁ y₁ * (r₂ - r₁)
        - barrierUy s₀ β A r₁ y₁ * (y₂ - y₁)
        - (1 / 2 : ℝ) * barrierUyy s₀ β A r₁ y₁ * (y₂ - y₁) ^ 2| ≤
      K * ((r₂ - r₁) ^ 2 + (r₂ - r₁) * |y₂ - y₁| + |y₂ - y₁| ^ 3))
    {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw_cont : ContinuousOn w (Icc 0 s₀))
    (hqv_sub : ∀ m : ℕ, ∀ j < 2 ^ m,
      Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.Ico (j * 2 ^ n) ((j + 1) * 2 ^ n),
          (w (((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ))) -
           w ((k : ℝ) * (s₀ / ((2 ^ (m + n) : ℕ) : ℝ)))) ^ 2)
        atTop (𝓝 (s₀ / ((2 ^ m : ℕ) : ℝ)))) :
    let grid (n k : ℕ) : ℝ := (k : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ))
    let Y (r : ℝ) : ℝ := x + w r
    let σ (r y : ℝ) : ℝ := y ^ 2 + barrierUy s₀ β A r y
    Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range (2 ^ n),
        (σ (grid n k) (Y (grid n k)) * (w (grid n (k + 1)) - w (grid n k)) -
          (1 / 2 : ℝ) * σ (grid n k) (Y (grid n k)) ^ 2 * (s₀ / ((2 ^ n : ℕ) : ℝ)))) atTop
      (𝓝 ((1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - (∫ r in (0 : ℝ)..s₀, Y r) -
        (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, Y r ^ 4) - barrierU s₀ β A 0 x -
        ∫ r in (0 : ℝ)..s₀,
          (barrierUr s₀ β A r (Y r) + Y r ^ 2 * barrierUy s₀ β A r (Y r) +
           (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r) + (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2))) := by
  intro grid Y σ
  have hY_cont : ContinuousOn Y (Icc 0 s₀) := continuousOn_const.add hw_cont
  -- Continuity of `barrierUr`, `barrierUy`, `barrierUyy` via `continuous_max.comp_continuousOn`
  have hy'_cont : ContinuousOn (fun r => max (Y r) (A / (2 * s₀))) (Icc 0 s₀) :=
    continuous_max.comp_continuousOn (hY_cont.prodMk continuousOn_const)
  have hy'_ne : ∀ r ∈ Icc 0 s₀, max (Y r) (A / (2 * s₀)) ≠ 0 := fun r _ =>
    ne_of_gt (lt_of_lt_of_le (div_pos hA (by positivity)) (le_max_right _ _))
  have hv_cont : ContinuousOn (fun r => max (s₀ - r - A / max (Y r) (A / (2 * s₀))) 0) (Icc 0 s₀) :=
    continuous_max.comp_continuousOn
      ((((continuousOn_const.sub continuousOn_id).sub (continuousOn_const.div hy'_cont hy'_ne))).prodMk
        continuousOn_const)
  have hur_cont : ContinuousOn (fun r => barrierUr s₀ β A r (Y r)) (Icc 0 s₀) :=
    (continuousOn_const.mul (hv_cont.pow 2)).congr fun r hr =>
      (barrierU_eq_clamped hs₀ hA hr.1 hr.2).2.1
  have huy_cont : ContinuousOn (fun r => barrierUy s₀ β A r (Y r)) (Icc 0 s₀) :=
    ((continuousOn_const.mul (hv_cont.pow 2)).mul
      (continuousOn_const.div (hy'_cont.pow 2) fun r hr => pow_ne_zero 2 (hy'_ne r hr))).congr
      fun r hr => (barrierU_eq_clamped hs₀ hA hr.1 hr.2).2.2.1
  have huyy_cont : ContinuousOn (fun r => barrierUyy s₀ β A r (Y r)) (Icc 0 s₀) :=
    (((continuousOn_const.mul hv_cont).mul ((continuousOn_const.div (hy'_cont.pow 2)
        fun r hr => pow_ne_zero 2 (hy'_ne r hr)).pow 2)).add
      ((continuousOn_const.mul (hv_cont.pow 2)).mul (continuousOn_const.div (hy'_cont.pow 3)
        fun r hr => pow_ne_zero 3 (hy'_ne r hr)))).congr
      fun r hr => (barrierU_eq_clamped hs₀ hA hr.1 hr.2).2.2.2
  -- Clean telescoping identity using a named `V : ℕ → ℝ` so `Finset.sum_range_sub` matches on the nose!
  have htel : ∀ n : ℕ,
      ∑ k ∈ Finset.range (2 ^ n),
        (σ (grid n k) (Y (grid n k)) * (w (grid n (k + 1)) - w (grid n k)) -
          (1 / 2 : ℝ) * σ (grid n k) (Y (grid n k)) ^ 2 * (s₀ / ((2 ^ n : ℕ) : ℝ))) =
      ((1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - barrierU s₀ β A 0 x)
      - ∑ k ∈ Finset.range (2 ^ n),
          (Y (grid n k) + (1 / 2 : ℝ) * barrierUyy s₀ β A (grid n k) (Y (grid n k))) *
            (w (grid n (k + 1)) - w (grid n k)) ^ 2
      - ∑ k ∈ Finset.range (2 ^ n),
          (barrierUr s₀ β A (grid n k) (Y (grid n k)) + (1 / 2 : ℝ) * σ (grid n k) (Y (grid n k)) ^ 2) *
            (s₀ / ((2 ^ n : ℕ) : ℝ))
      - ∑ k ∈ Finset.range (2 ^ n),
          ((1 / 3 : ℝ) * (w (grid n (k + 1)) - w (grid n k)) ^ 3 +
           (barrierU s₀ β A (grid n (k + 1)) (Y (grid n (k + 1))) -
            barrierU s₀ β A (grid n k) (Y (grid n k)) -
            barrierUr s₀ β A (grid n k) (Y (grid n k)) * (s₀ / ((2 ^ n : ℕ) : ℝ)) -
            barrierUy s₀ β A (grid n k) (Y (grid n k)) * (w (grid n (k + 1)) - w (grid n k)) -
            (1 / 2 : ℝ) * barrierUyy s₀ β A (grid n k) (Y (grid n k)) *
              (w (grid n (k + 1)) - w (grid n k)) ^ 2)) := by
    intro n
    let V : ℕ → ℝ := fun k => (1 / 3 : ℝ) * Y (grid n k) ^ 3 + barrierU s₀ β A (grid n k) (Y (grid n k))
    have hV : ∑ k ∈ Finset.range (2 ^ n), (V (k + 1) - V k) =
        (1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - barrierU s₀ β A 0 x := by
      rw [Finset.sum_range_sub V (2 ^ n)]
      have hN : grid n (2 ^ n) = s₀ := by simp only [grid]; field_simp
      have h0 : grid n 0 = 0 := by simp [grid]
      have hY0 : Y 0 = x := by simp [Y, hw0]
      simp only [V, hN, h0, hY0, barrierU_terminal s₀ β A (Y s₀) hs₀ hA]
      ring
    rw [← hV, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hinc : Y (grid n (k + 1)) = Y (grid n k) + (w (grid n (k + 1)) - w (grid n k)) := by
      simp only [Y]; ring
    simp only [V, σ]; rw [hinc]; ring
  -- Limit 1: QV sum
  have hL1 := tendsto_dyadic_weighted_qv_of_subintervals (w := w)
    (g := fun r => Y r + (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r))
    hs₀ hqv_sub (hY_cont.add (continuousOn_const.mul huyy_cont))
  -- Limit 2: Riemann sum
  have hL2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        (barrierUr s₀ β A (grid n k) (Y (grid n k)) + (1 / 2 : ℝ) * σ (grid n k) (Y (grid n k)) ^ 2) *
          (s₀ / ((2 ^ n : ℕ) : ℝ))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s₀, (barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * σ r (Y r) ^ 2))) := by
    have h := (tendsto_lebRiemann_of_continuousOn
      (g := fun r => barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * σ r (Y r) ^ 2) hs₀.le
      (hur_cont.add ((continuousOn_const :
          ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 s₀)).mul
        (((hY_cont.pow 2).add huy_cont).pow 2)))).comp
      (StrictMono.tendsto_atTop (fun a b hab => Nat.sub_lt_sub_right (Nat.one_le_two_pow)
        (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hab)))
    refine h.congr fun n => ?_
    have h2n : (2 ^ n - 1 : ℕ) + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
    have hcast : ((2 ^ n - 1 : ℕ) : ℝ) + 1 = ((2 ^ n : ℕ) : ℝ) := by
      rw [← Nat.cast_add_one, h2n]
    simp only [Function.comp_def, grid, σ, h2n, hcast]
  -- Limit 3: Remainder sum → 0
  have hL3 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
        ((1 / 3 : ℝ) * (w (grid n (k + 1)) - w (grid n k)) ^ 3 +
         (barrierU s₀ β A (grid n (k + 1)) (Y (grid n (k + 1))) -
          barrierU s₀ β A (grid n k) (Y (grid n k)) -
          barrierUr s₀ β A (grid n k) (Y (grid n k)) * (s₀ / ((2 ^ n : ℕ) : ℝ)) -
          barrierUy s₀ β A (grid n k) (Y (grid n k)) * (w (grid n (k + 1)) - w (grid n k)) -
          (1 / 2 : ℝ) * barrierUyy s₀ β A (grid n k) (Y (grid n k)) *
            (w (grid n (k + 1)) - w (grid n k)) ^ 2))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    have htot_qv := tendsto_dyadic_weighted_qv_of_subintervals hs₀ hqv_sub (g := fun _ => (1 : ℝ)) continuousOn_const
    simp only [one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at htot_qv
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp htot_qv) 1 one_pos
    set η_w : ℝ := ε / (2 * (((1 / 3 : ℝ) + K) * (s₀ + 1) + K * s₀ + 1))
    have hη_w : 0 < η_w := by positivity
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hw_cont
    obtain ⟨δ, hδ, hδ_bd⟩ := Metric.uniformContinuousOn_iff_le.mp huc η_w hη_w
    have hΔ_zero : Tendsto (fun n : ℕ => s₀ / ((2 ^ n : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.comp
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)))
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hΔ_zero) (min δ (ε / (2 * (K * s₀ + 1)))) (lt_min hδ (by positivity))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hqv_le : ∑ k ∈ Finset.range (2 ^ n), (w (grid n (k + 1)) - w (grid n k)) ^ 2 ≤ s₀ + 1 := by
      have h := hN₁ n (le_trans (le_max_left _ _) hn); rw [Real.dist_eq, abs_lt] at h; linarith
    have hΔ_lt : s₀ / ((2 ^ n : ℕ) : ℝ) < min δ (ε / (2 * (K * s₀ + 1))) := by
      have h := hN₂ n (le_trans (le_max_right _ _) hn)
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at h; exact h
    have hdw : ∀ k ∈ Finset.range (2 ^ n), |w (grid n (k + 1)) - w (grid n k)| ≤ η_w := fun k hk => by
      have hk' := Finset.mem_range.mp hk
      have hsub : grid n (k + 1) - grid n k = s₀ / ((2 ^ n : ℕ) : ℝ) := by simp only [grid]; push_cast; ring
      have hdist : dist (grid n (k + 1)) (grid n k) ≤ δ := by
        rw [Real.dist_eq, hsub, abs_of_pos (by positivity)]; exact (lt_of_lt_of_le hΔ_lt (min_le_left _ _)).le
      have hg1 : grid n (k + 1) ∈ Icc 0 s₀ := ⟨by simp only [grid]; positivity, by
        simp only [grid]; calc ((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) ≤
          ((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk') (by positivity)
          _ = s₀ := by field_simp⟩
      have hg0 : grid n k ∈ Icc 0 s₀ := ⟨by simp only [grid]; positivity, by linarith [hg1.2, hsub, show 0 < s₀ / ((2 ^ n : ℕ) : ℝ) by positivity]⟩
      simpa [Real.dist_eq] using hδ_bd _ hg1 _ hg0 hdist
    rw [Real.dist_eq, sub_zero]
    calc |∑ k ∈ Finset.range (2 ^ n), _|
        ≤ ∑ k ∈ Finset.range (2 ^ n),
            (((1 / 3 : ℝ) + K) * η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 +
             K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 + (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          have hk' := Finset.mem_range.mp hk
          have hsub : grid n (k + 1) - grid n k = s₀ / ((2 ^ n : ℕ) : ℝ) := by simp only [grid]; push_cast; ring
          have hYsub : Y (grid n (k + 1)) - Y (grid n k) = w (grid n (k + 1)) - w (grid n k) := by simp only [Y]; ring
          have hgk1 : grid n (k + 1) ≤ s₀ := by
            simp only [grid]; calc ((k + 1 : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) ≤
              ((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk') (by positivity)
              _ = s₀ := by field_simp
          have ht := htay (grid n k) (grid n (k + 1)) (Y (grid n k)) (Y (grid n (k + 1)))
            (by simp only [grid]; positivity) (by linarith [hsub, show 0 < s₀ / ((2 ^ n : ℕ) : ℝ) by positivity]) hgk1
          rw [hsub, hYsub] at ht
          have hdw_k := hdw k hk
          have hcube3 : |w (grid n (k + 1)) - w (grid n k)| ^ 3 ≤
              η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 := by
            rw [pow_succ', sq_abs]; exact mul_le_mul_of_nonneg_right hdw_k (sq_nonneg _)
          have hcube1 : |(1 / 3 : ℝ) * (w (grid n (k + 1)) - w (grid n k)) ^ 3| ≤
              (1 / 3 : ℝ) * η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 := by
            rw [abs_mul, abs_of_pos (by norm_num), abs_pow]
            calc (1 / 3 : ℝ) * |w (grid n (k + 1)) - w (grid n k)| ^ 3
                ≤ (1 / 3 : ℝ) * (η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2) :=
                  mul_le_mul_of_nonneg_left hcube3 (by norm_num)
              _ = _ := by ring
          have hK_step : K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 + (s₀ / ((2 ^ n : ℕ) : ℝ)) *
                |w (grid n (k + 1)) - w (grid n k)| + |w (grid n (k + 1)) - w (grid n k)| ^ 3) ≤
              K * η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 +
                K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 + (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w) := by
            have h1 := mul_le_mul_of_nonneg_left hdw_k (show 0 ≤ s₀ / ((2 ^ n : ℕ) : ℝ) by positivity)
            have hinner :
                (s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                    (s₀ / ((2 ^ n : ℕ) : ℝ)) * |w (grid n (k + 1)) - w (grid n k)| +
                    |w (grid n (k + 1)) - w (grid n k)| ^ 3 ≤
                  (s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                    (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w +
                    η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 :=
              add_le_add (add_le_add le_rfl h1) hcube3
            have hKmul := mul_le_mul_of_nonneg_left hinner hK0
            have hre :
                K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                    (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w +
                    η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2) =
                  K * η_w * (w (grid n (k + 1)) - w (grid n k)) ^ 2 +
                    K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                      (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w) := by ring
            exact hKmul.trans_eq hre
          exact (abs_add_le _ _).trans (by linarith)
      _ = ((1 / 3 : ℝ) + K) * η_w * (∑ k ∈ Finset.range (2 ^ n), (w (grid n (k + 1)) - w (grid n k)) ^ 2) +
          K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) + K * s₀ * η_w := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have h2s : ((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) = s₀ := by field_simp
          have h2s2 : ((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 = s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) := by
            rw [sq, ← mul_assoc, h2s]
          have hdist : ((2 ^ n : ℕ) : ℝ) * (K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w)) =
              K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) + K * s₀ * η_w := by
            have hdistrib :
                ((2 ^ n : ℕ) : ℝ) * (K * ((s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2 +
                  (s₀ / ((2 ^ n : ℕ) : ℝ)) * η_w)) =
              K * (((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ)) ^ 2) +
                K * (((2 ^ n : ℕ) : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ))) * η_w := by ring
            rw [hdistrib, h2s2, h2s]
            ring
          rw [hdist]
          ring
      _ ≤ ((1 / 3 : ℝ) + K) * η_w * (s₀ + 1) + K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) + K * s₀ * η_w := by gcongr
      _ < ε / 2 + ε / 2 := by
          have h1 : ((1 / 3 : ℝ) + K) * η_w * (s₀ + 1) + K * s₀ * η_w < ε / 2 := by
            have hfac : ((1 / 3 : ℝ) + K) * η_w * (s₀ + 1) + K * s₀ * η_w =
                (((1 / 3 : ℝ) + K) * (s₀ + 1) + K * s₀) * η_w := by ring
            rw [hfac]
            set num : ℝ := ((1 / 3 : ℝ) + K) * (s₀ + 1) + K * s₀
            set denPart : ℝ := num + 1
            have hdenPart : 0 < denPart := by positivity
            have hfrac : num / denPart < 1 := (div_lt_one hdenPart).mpr (by linarith)
            simp only [η_w]
            have hrew : num * (ε / (2 * denPart)) = (num / denPart) * (ε / 2) := by field_simp
            rw [hrew]
            have : (num / denPart) * (ε / 2) < 1 * (ε / 2) :=
              mul_lt_mul_of_pos_right hfrac (half_pos hε)
            simpa using this
          have h2 : K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) < ε / 2 := by
            have hlt := lt_of_lt_of_le hΔ_lt (min_le_right _ _)
            have hden : 0 < 2 * (K * s₀ + 1) := by positivity
            have hle : K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) ≤
                K * s₀ * (ε / (2 * (K * s₀ + 1))) :=
              mul_le_mul_of_nonneg_left hlt.le (by positivity)
            have hlt2 : K * s₀ * (ε / (2 * (K * s₀ + 1))) < ε / 2 := by
              set num : ℝ := K * s₀
              set denPart : ℝ := num + 1
              have hdenPart : 0 < denPart := by positivity
              have hfrac : num / denPart < 1 := (div_lt_one hdenPart).mpr (by linarith)
              have hrew : num * (ε / (2 * denPart)) = (num / denPart) * (ε / 2) := by field_simp
              rw [hrew]
              have : (num / denPart) * (ε / 2) < 1 * (ε / 2) :=
                mul_lt_mul_of_pos_right hfrac (half_pos hε)
              simpa using this
            exact hle.trans_lt hlt2
          have hsum : ((1 / 3 : ℝ) + K) * η_w * (s₀ + 1) + K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) +
              K * s₀ * η_w =
            (((1 / 3 : ℝ) + K) * η_w * (s₀ + 1) + K * s₀ * η_w) +
              K * s₀ * (s₀ / ((2 ^ n : ℕ) : ℝ)) := by ring
          rw [hsum]
          exact add_lt_add h1 h2
      _ = ε := add_halves ε
  -- Assemble all 3 limits
  have hcomb := (((tendsto_const_nhds (x := (1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - barrierU s₀ β A 0 x)).sub hL1).sub hL2).sub hL3
  have hi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 s₀) → IntervalIntegrable g volume 0 s₀ :=
    fun hg => hg.intervalIntegrable_of_Icc hs₀.le
  have hI1 : ∫ r in (0 : ℝ)..s₀, (Y r + (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r)) =
      (∫ r in (0 : ℝ)..s₀, Y r) + (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r)) :=
    intervalIntegral.integral_add (hi hY_cont) (hi (continuousOn_const.mul huyy_cont))
  have hI2 : ∫ r in (0 : ℝ)..s₀, (barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * σ r (Y r) ^ 2) =
      (∫ r in (0 : ℝ)..s₀, barrierUr s₀ β A r (Y r)) + (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * Y r ^ 4) +
      (∫ r in (0 : ℝ)..s₀, Y r ^ 2 * barrierUy s₀ β A r (Y r)) +
      (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) := by
    have hexp : ∀ r, barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * σ r (Y r) ^ 2 =
        barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * Y r ^ 4 + Y r ^ 2 * barrierUy s₀ β A r (Y r) +
        (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2 := fun r => by simp only [σ]; ring
    simp_rw [hexp]
    have hf1 : IntervalIntegrable (fun r => barrierUr s₀ β A r (Y r)) volume 0 s₀ := hi hur_cont
    have hf2 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * Y r ^ 4) volume 0 s₀ :=
      hi ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 s₀)).mul (hY_cont.pow 4))
    have hf3 : IntervalIntegrable (fun r => Y r ^ 2 * barrierUy s₀ β A r (Y r)) volume 0 s₀ :=
      hi ((hY_cont.pow 2).mul huy_cont)
    have hf4 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) volume 0 s₀ :=
      hi ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 s₀)).mul (huy_cont.pow 2))
    rw [intervalIntegral.integral_add
      (f := fun r => barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * Y r ^ 4 +
        Y r ^ 2 * barrierUy s₀ β A r (Y r))
      (g := fun r => (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2)
      ((hf1.add hf2).add hf3) hf4,
      intervalIntegral.integral_add
        (f := fun r => barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * Y r ^ 4)
        (g := fun r => Y r ^ 2 * barrierUy s₀ β A r (Y r))
        (hf1.add hf2) hf3,
      intervalIntegral.integral_add (f := fun r => barrierUr s₀ β A r (Y r))
        (g := fun r => (1 / 2 : ℝ) * Y r ^ 4) hf1 hf2]
  have hI3 : ∫ r in (0 : ℝ)..s₀, (barrierUr s₀ β A r (Y r) + Y r ^ 2 * barrierUy s₀ β A r (Y r) +
        (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r) + (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) =
      (∫ r in (0 : ℝ)..s₀, barrierUr s₀ β A r (Y r)) + (∫ r in (0 : ℝ)..s₀, Y r ^ 2 * barrierUy s₀ β A r (Y r)) +
      (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r)) +
      (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) := by
    have hg1 : IntervalIntegrable (fun r => barrierUr s₀ β A r (Y r)) volume 0 s₀ := hi hur_cont
    have hg2 : IntervalIntegrable (fun r => Y r ^ 2 * barrierUy s₀ β A r (Y r)) volume 0 s₀ :=
      hi ((hY_cont.pow 2).mul huy_cont)
    have hg3 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r)) volume 0 s₀ :=
      hi ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 s₀)).mul huyy_cont)
    have hg4 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) volume 0 s₀ :=
      hi ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 s₀)).mul (huy_cont.pow 2))
    rw [intervalIntegral.integral_add
      (f := fun r => barrierUr s₀ β A r (Y r) + Y r ^ 2 * barrierUy s₀ β A r (Y r) +
        (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r))
      (g := fun r => (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2)
      ((hg1.add hg2).add hg3) hg4,
      intervalIntegral.integral_add
        (f := fun r => barrierUr s₀ β A r (Y r) + Y r ^ 2 * barrierUy s₀ β A r (Y r))
        (g := fun r => (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r))
        (hg1.add hg2) hg3,
      intervalIntegral.integral_add (f := fun r => barrierUr s₀ β A r (Y r))
        (g := fun r => Y r ^ 2 * barrierUy s₀ β A r (Y r)) hg1 hg2]
  have hI4 : ∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * Y r ^ 4 = (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..s₀, Y r ^ 4 :=
    intervalIntegral.integral_const_mul _ _
  have htarget :
      ((1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - barrierU s₀ β A 0 x) -
        (∫ r in (0 : ℝ)..s₀, (Y r + (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r))) -
        (∫ r in (0 : ℝ)..s₀, (barrierUr s₀ β A r (Y r) + (1 / 2 : ℝ) * σ r (Y r) ^ 2)) - 0 =
      (1 / 3 : ℝ) * (Y s₀ ^ 3 - x ^ 3) - (∫ r in (0 : ℝ)..s₀, Y r) -
        (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, Y r ^ 4) - barrierU s₀ β A 0 x -
        ∫ r in (0 : ℝ)..s₀, (barrierUr s₀ β A r (Y r) + Y r ^ 2 * barrierUy s₀ β A r (Y r) +
          (1 / 2 : ℝ) * barrierUyy s₀ β A r (Y r) + (1 / 2 : ℝ) * barrierUy s₀ β A r (Y r) ^ 2) := by
    rw [hI1, hI2, hI3, hI4]; ring
  rw [htarget] at hcomb
  exact hcomb.congr fun n => (htel n).symm

/-! ### Part 6: Measurability helpers & short main theorem -/

private lemma measurable_counterexampleV1Exponent' {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (x : ℝ) :
    Measurable (counterexampleV1Exponent B hd s₀ x) := by
  have hlim : ∀ ω, Tendsto (fun n : ℕ =>
      (1 / 3 : ℝ) * ((x + MultiBrownian.W B s₀ ω ⟨0, hd⟩) ^ 3 - x ^ 3) -
      (∑ k ∈ Finset.range (n + 1), (x + MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
        (s₀ / ((n : ℝ) + 1))) -
      (1 / 2 : ℝ) * (∑ k ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 * (s₀ / ((n : ℝ) + 1))))
      atTop (𝓝 (counterexampleV1Exponent B hd s₀ x ω)) := fun ω =>
    ((tendsto_const_nhds.sub (tendsto_lebRiemann_of_continuousOn hs₀
      (continuousOn_const.add (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn))).sub
      ((tendsto_lebRiemann_of_continuousOn hs₀
        ((continuousOn_const.add (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn).pow 4)).const_mul _))
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
  exact (((measurable_const.mul (((measurable_const.add (MultiBrownian.W_meas B s₀ ⟨0, hd⟩)).pow_const 3).sub
    measurable_const)).sub (Finset.measurable_sum _ fun k _ =>
      (measurable_const.add (MultiBrownian.W_meas B _ ⟨0, hd⟩)).mul measurable_const)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      ((measurable_const.add (MultiBrownian.W_meas B _ ⟨0, hd⟩)).pow_const 4).mul measurable_const)))

private lemma measurable_barrierUy_y (s₀ β A r : ℝ) :
    Measurable (fun y : ℝ => barrierUy s₀ β A r y) := by
  unfold barrierUy
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt (measurable_const.div measurable_id) measurable_const)
  · exact (measurable_const.mul ((measurable_const.sub (measurable_const.div measurable_id)).pow_const 2)).mul
      (measurable_const.div (measurable_id.pow_const 2))

/-- **B4b (short ~45-line assembly — zero timeouts!).** -/
lemma integral_exp_shiftedExponent_le_exp_barrierU {d : ℕ}
    (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ β A x : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β)
    (hA2 : 2 ≤ A) (hAs : 2 * Real.sqrt (s₀ ^ 3) ≤ A)
    (hAβ : 2 * Real.sqrt β * s₀ ^ 3 ≤ A)
    (_hx : 2 * A / s₀ ≤ x) :
    (∫ ω, Real.exp (counterexampleV1Exponent B hd s₀ x ω) ∂P) ≤
      Real.exp (barrierU s₀ β A 0 x) := by
  have hA : 0 < A := by linarith
  let grid (n k : ℕ) : ℝ := (k : ℝ) * (s₀ / ((2 ^ n : ℕ) : ℝ))
  let σ (r y : ℝ) : ℝ := y ^ 2 + barrierUy s₀ β A r y
  let logD (n : ℕ) (ω : Ω) : ℝ :=
    ∑ k ∈ Finset.range (2 ^ n),
      (σ (grid n k) (x + MultiBrownian.W B (grid n k) ω ⟨0, hd⟩) *
        wnnIncr B ⟨0, hd⟩ (grid n k) (grid n (k + 1)) ω -
      (1 / 2 : ℝ) * σ (grid n k) (x + MultiBrownian.W B (grid n k) ω ⟨0, hd⟩) ^ 2 *
        (s₀ / ((2 ^ n : ℕ) : ℝ)))
  have hσ_meas : ∀ r, Measurable (fun y : ℝ => σ r (x + y)) := fun r =>
    ((measurable_const.add measurable_id).pow_const 2).add
      ((measurable_barrierUy_y s₀ β A r).comp (measurable_const.add measurable_id))
  have hD_one : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (logD n ω)) ∂P = 1 := fun n =>
    lintegral_discrete_doleans_eq_one B hd hs₀.le (2 ^ n) (by positivity)
      (fun k ω => σ (grid n k) (x + MultiBrownian.W B (grid n k) ω ⟨0, hd⟩))
      (fun k _ => (hσ_meas (grid n k)).comp (measurable_W_pathFiltration B ⟨grid n k, by positivity, le_rfl⟩ ⟨0, hd⟩))
      (2 ^ n) le_rfl
  obtain ⟨K, hK0, htay⟩ := barrierU_taylor_rem hs₀ hβ hA
  have hlim_ae : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => logD n ω) atTop
        (𝓝 (counterexampleV1Exponent B hd s₀ x ω - barrierU s₀ β A 0 x -
          ∫ r in (0 : ℝ)..s₀,
            (barrierUr s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
             (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 2 *
               barrierUy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
             (1 / 2 : ℝ) * barrierUyy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
             (1 / 2 : ℝ) * barrierUy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 2))) := by
    filter_upwards [ae_dyadic_subinterval_qv B ⟨0, hd⟩ hs₀] with ω hqv
    simpa only [logD, σ, grid, wnnIncr_eq_W, counterexampleV1Exponent] using
      tendsto_logD_of_qv hs₀ hβ hA hK0 htay (MultiBrownian.W_zero B ω ⟨0, hd⟩)
        (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn hqv
  have hdrift_nonpos : ∀ ω,
      ∫ r in (0 : ℝ)..s₀,
        (barrierUr s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
         (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 2 *
           barrierUy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
         (1 / 2 : ℝ) * barrierUyy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) +
         (1 / 2 : ℝ) * barrierUy s₀ β A r (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 2) ≤ 0 := fun ω => by
    refine neg_nonneg.mp ?_
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_nonneg hs₀.le fun r hr => neg_nonneg.mpr ?_
    unfold barrierUr barrierUy barrierUyy
    split_ifs with h
    · exact barrierU_pde_nonpos hs₀ hβ hA2 hAs hAβ hr.1 hr.2 h.1 h.2
    · norm_num
  have hlogD_meas : ∀ n, Measurable (logD n) := fun n =>
    Finset.measurable_sum _ fun k _ =>
      (((hσ_meas (grid n k)).comp (MultiBrownian.W_meas B (grid n k) ⟨0, hd⟩)).mul
        (measurable_wnnIncr B ⟨0, hd⟩ _ _)).sub
        (((((hσ_meas (grid n k)).comp (MultiBrownian.W_meas B (grid n k) ⟨0, hd⟩)).pow_const 2).const_mul _).mul_const _)
  have hfatou : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω -
        barrierU s₀ β A 0 x)) ∂P ≤ 1 := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω -
            barrierU s₀ β A 0 x)) ∂P
        ≤ ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Real.exp (logD n ω))) atTop ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hlim_ae] with ω hω
          have hlim_enn := ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp hω)
          simp only [Function.comp_def] at hlim_enn
          rw [hlim_enn.liminf_eq]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hdrift_nonpos ω]))
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (logD n ω)) ∂P) atTop :=
          lintegral_liminf_le fun n => ((hlogD_meas n).exp).ennreal_ofReal
      _ = 1 := by simp_rw [hD_one]; exact liminf_const 1
  have hV1_meas := measurable_counterexampleV1Exponent' B hd hs₀.le x
  have hlint_le : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x)) := by
    have heq : ∀ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) =
        ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x)) *
          ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω - barrierU s₀ β A 0 x)) :=
      fun ω => by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_sub_cancel]
    simp_rw [heq]
    have hf : Measurable fun ω =>
        ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω - barrierU s₀ β A 0 x)) :=
      ((hV1_meas.sub_const (barrierU s₀ β A 0 x)).exp).ennreal_ofReal
    rw [lintegral_const_mul (ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x))) hf]
    calc ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω - barrierU s₀ β A 0 x)) ∂P
        ≤ ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x)) * 1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (barrierU s₀ β A 0 x)) := mul_one _
  have hint : Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s₀ x ω)) P :=
    ⟨hV1_meas.exp.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_enorm]; simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      exact hlint_le.trans_lt ENNReal.ofReal_lt_top⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact hlint_le

end SignatureVolatility
