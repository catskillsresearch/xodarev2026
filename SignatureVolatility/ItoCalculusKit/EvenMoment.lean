module

public import SignatureVolatility.ItoCalculusKit.EighthMoment


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SignatureVolatility

/-!
# Sixteenth moments of martingale-difference sums

`integral_sum_pow_sixteen_le_of_orthogonal`: if `𝔼[(∑_{i<j} ξ_i)¹⁵ ξ_j] = 0` for every `j`, then
`‖∑_{i<m} ξ_i‖₁₆² ≤ c₁₆ ∑_{i<m} ‖ξ_i‖₁₆²` with `‖ξ‖₁₆² = (𝔼 ξ¹⁶)^{1/8}`.

The one-step estimate uses the second-order Taylor bound
`|(a+b)^{n+2} - a^{n+2} - (n+2) a^{n+1} b| ≤ ((n+2)(n+1)/2) b² (|a|+|b|)^n`, the orthogonality to kill
the linear term, and Hölder for `𝔼[X² M¹⁴]`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Second-order Taylor remainder bound for powers. -/
lemma abs_add_pow_sub_taylor_le (a b : ℝ) (n : ℕ) :
    |(a + b) ^ (n + 2) - a ^ (n + 2) - (n + 2) * a ^ (n + 1) * b| ≤
      ((n + 2) * (n + 1) / 2) * b ^ 2 * (|a| + |b|) ^ n := by
  induction n with
  | zero => simp only [CharP.cast_eq_zero, pow_zero, mul_one]; norm_num; rw [abs_of_nonneg (by nlinarith [sq_nonneg b])]; nlinarith [sq_nonneg b]
  | succ n ih =>
    have key : (a + b) ^ (n + 1 + 2) - a ^ (n + 1 + 2) - ((↑(n + 1) : ℝ) + 2) * a ^ (n + 1 + 1) * b
        = (a + b) * ((a + b) ^ (n + 2) - a ^ (n + 2) - (n + 2) * a ^ (n + 1) * b) +
          (n + 2) * a ^ (n + 1) * b ^ 2 := by push_cast; ring
    rw [key]
    have hab : |a + b| ≤ |a| + |b| := abs_add_le a b
    have h0 : 0 ≤ |a| + |b| := by positivity
    have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
    have hapow : |a| ^ (n + 1) ≤ (|a| + |b|) ^ (n + 1) :=
      pow_le_pow_left₀ (abs_nonneg a) (by linarith [abs_nonneg b]) _
    calc |(a + b) * ((a + b) ^ (n + 2) - a ^ (n + 2) - (n + 2) * a ^ (n + 1) * b) +
          (n + 2) * a ^ (n + 1) * b ^ 2|
        ≤ |a + b| * |(a + b) ^ (n + 2) - a ^ (n + 2) - (n + 2) * a ^ (n + 1) * b| +
          (n + 2) * |a| ^ (n + 1) * b ^ 2 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hb2,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2)]
      _ ≤ (|a| + |b|) * (((n + 2) * (n + 1) / 2) * b ^ 2 * (|a| + |b|) ^ n) +
          (n + 2) * (|a| + |b|) ^ (n + 1) * b ^ 2 := by
          gcongr
      _ = ((↑(n + 1) + 2) * (↑(n + 1) + 1) / 2) * b ^ 2 * (|a| + |b|) ^ (n + 1) := by
          push_cast; ring

/-- Pointwise sixteenth-power expansion with the linear term kept exact. -/
lemma add_pow_sixteen_le (a b : ℝ) :
    (a + b) ^ 16 ≤ a ^ 16 + 16 * (a ^ 15 * b) +
      983040 * (b ^ 2 * a ^ 14 + b ^ 16) := by
  have h := abs_add_pow_sub_taylor_le a b 14
  norm_num at h
  have h2 : (|a| + |b|) ^ 14 ≤ 2 ^ 13 * (|a| ^ 14 + |b| ^ 14) :=
    add_pow_le (abs_nonneg a) (abs_nonneg b) 14
  have ea : |a| ^ 14 = a ^ 14 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have eb : |b| ^ 14 = b ^ 14 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [ea, eb] at h2
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have h3 : b ^ 2 * (|a| + |b|) ^ 14 ≤ b ^ 2 * (2 ^ 13 * (a ^ 14 + b ^ 14)) :=
    mul_le_mul_of_nonneg_left h2 hb2
  have h4 := (abs_le.mp h).2
  have e16 : b ^ 2 * b ^ 14 = b ^ 16 := by ring
  nlinarith [h3, h4, e16]

private lemma abs_pow_mul_pow_le_sixteen (a b : ℝ) {p q : ℕ} (h : p + q = 16) :
    |a ^ p * b ^ q| ≤ a ^ 16 + b ^ 16 := by
  rw [abs_mul, abs_pow, abs_pow]
  have ha8 : |a| ^ 16 = a ^ 16 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hb8 : |b| ^ 16 = b ^ 16 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have ha0 : 0 ≤ a ^ 16 := by positivity
  have hb0 : 0 ≤ b ^ 16 := by positivity
  rcases le_total |a| |b| with hab | hab
  · calc |a| ^ p * |b| ^ q ≤ |b| ^ p * |b| ^ q := by gcongr
      _ = |b| ^ 16 := by rw [← pow_add, h]
      _ ≤ a ^ 16 + b ^ 16 := by rw [hb8]; linarith
  · calc |a| ^ p * |b| ^ q ≤ |a| ^ p * |a| ^ q := by gcongr
      _ = |a| ^ 16 := by rw [← pow_add, h]
      _ ≤ a ^ 16 + b ^ 16 := by rw [ha8]; linarith

omit [IsProbabilityMeasure P] in
/-- Mixed sixteenth-order monomials of two `L¹⁶` variables are integrable. -/
lemma integrable_pow_mul_pow_of_memLp_sixteen [IsFiniteMeasure P] {f g : Ω → ℝ}
    (hf : MemLp f 16 P) (hg : MemLp g 16 P) {p q : ℕ} (h : p + q = 16) :
    Integrable (fun ω => f ω ^ p * g ω ^ q) P := by
  have hf8 : Integrable (fun ω => ‖f ω‖ ^ 16) P := by
    simpa using (hf.integrable_norm_pow' (p := 16))
  have hg8 : Integrable (fun ω => ‖g ω‖ ^ 16) P := by
    simpa using (hg.integrable_norm_pow' (p := 16))
  refine Integrable.mono' (hf8.fun_add hg8)
    ((hf.aestronglyMeasurable.pow p).mul (hg.aestronglyMeasurable.pow q))
    (ae_of_all _ fun ω => ?_)
  have h1 := abs_pow_mul_pow_le_sixteen (f ω) (g ω) h
  have e1 : ‖f ω‖ ^ 16 = f ω ^ 16 := by
    rw [Real.norm_eq_abs, ← abs_pow]; exact abs_of_nonneg (by positivity)
  have e2 : ‖g ω‖ ^ 16 = g ω ^ 16 := by
    rw [Real.norm_eq_abs, ← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [e1, e2]
  simpa [Real.norm_eq_abs] using h1

/-- Squared `L¹⁶` norm from the sixteenth moment: `a ↦ a^{1/8}`. -/
noncomputable def sq16 (a : ℝ) : ℝ := a ^ (1 / 8 : ℝ)

lemma sq16_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ sq16 a := Real.rpow_nonneg ha _

lemma sq16_pow_eight {a : ℝ} (ha : 0 ≤ a) : sq16 a ^ 8 = a := by
  unfold sq16
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

lemma sq16_le_of_le_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b ^ 8) : sq16 a ≤ b := by
  unfold sq16
  calc a ^ (1 / 8 : ℝ) ≤ (b ^ 8) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow ha h (by norm_num)
    _ = b := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num


/-- Hölder: `𝔼[X² M¹⁴] ≤ ‖X‖₁₆² ‖M‖₁₆¹⁴`. -/
lemma integral_sq_mul_pow14_le {X M : Ω → ℝ} (hX : MemLp X 16 P) (hM : MemLp M 16 P) :
    ∫ ω, X ω ^ 2 * M ω ^ 14 ∂P ≤
      sq16 (∫ ω, X ω ^ 16 ∂P) * sq16 (∫ ω, M ω ^ 16 ∂P) ^ 7 := by
  have hpq : (8 : ℝ).HolderConjugate (8 / 7) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf : MemLp (fun ω => X ω ^ 2) (ENNReal.ofReal 8) P := by
    have h := hX.norm_rpow_div 2
    have e1 : (16 : ℝ≥0∞) / 2 = ENNReal.ofReal 8 := by
      rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [e1] at h
    refine h.congr_norm ?_ ?_ |>.mono_exponent le_rfl
    · exact (hX.aestronglyMeasurable.pow 2)
    · refine ae_of_all _ fun ω => ?_
      simp [Real.norm_eq_abs, sq_abs]
  have hg : MemLp (fun ω => (M ω ^ 2) ^ 7) (ENNReal.ofReal (8 / 7)) P := by
    have h := hM.norm_rpow_div 14
    have e1 : (16 : ℝ≥0∞) / 14 = ENNReal.ofReal (8 / 7) := by
      rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
        show (14 : ℝ≥0∞) = ENNReal.ofReal 14 by norm_num, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [e1] at h
    refine h.congr_norm ?_ ?_
    · exact ((hM.aestronglyMeasurable.pow 2).pow 7)
    · refine ae_of_all _ fun ω => ?_
      have : ((14 : ℝ≥0∞)).toReal = ((14 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
      norm_num [Real.norm_eq_abs, ← pow_mul, abs_pow, abs_abs]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun ω => sq_nonneg (X ω))
    (ae_of_all _ fun ω => by positivity) hf hg
  have e1 : ∀ ω, (X ω ^ 2) ^ (8 : ℝ) = X ω ^ 16 := fun ω => by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
  have e2 : ∀ ω, ((M ω ^ 2) ^ 7) ^ (8 / 7 : ℝ) = M ω ^ 16 := fun ω => by
    rw [← Real.rpow_natCast (M ω ^ 2) 7, ← Real.rpow_mul (sq_nonneg _),
      show ((7 : ℕ) : ℝ) * (8 / 7) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
  simp only [e1, e2] at h
  have hA : 0 ≤ ∫ ω, M ω ^ 16 ∂P := integral_nonneg fun ω => by positivity
  have e3 : (∫ ω, M ω ^ 16 ∂P) ^ (1 / (8 / 7) : ℝ) = sq16 (∫ ω, M ω ^ 16 ∂P) ^ 7 := by
    unfold sq16
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num
  have e4 : (∫ ω, X ω ^ 2 * (M ω ^ 2) ^ 7 ∂P) = ∫ ω, X ω ^ 2 * M ω ^ 14 ∂P := by
    congr 1; funext ω; ring
  rw [e3, e4] at h
  exact h

/-- One martingale step in squared `L¹⁶` norm. -/
lemma sq16_add_le {M X : Ω → ℝ} (hM : MemLp M 16 P) (hX : MemLp X 16 P)
    (horth : ∫ ω, M ω ^ 15 * X ω ∂P = 0) :
    sq16 (∫ ω, (M ω + X ω) ^ 16 ∂P) ≤
      sq16 (∫ ω, M ω ^ 16 ∂P) + 983040 * sq16 (∫ ω, X ω ^ 16 ∂P) := by
  set A := ∫ ω, M ω ^ 16 ∂P
  set Bx := ∫ ω, X ω ^ 16 ∂P
  have hA : 0 ≤ A := integral_nonneg fun ω => by positivity
  have hB : 0 ≤ Bx := integral_nonneg fun ω => by positivity
  set m := sq16 A
  set x := sq16 Bx
  have hm : 0 ≤ m := sq16_nonneg hA
  have hx : 0 ≤ x := sq16_nonneg hB
  have iM : Integrable (fun ω => M ω ^ 16) P := by
    simpa using integrable_pow_mul_pow_of_memLp_sixteen hM hX (p := 16) (q := 0) rfl
  have iX : Integrable (fun ω => X ω ^ 16) P := by
    simpa using integrable_pow_mul_pow_of_memLp_sixteen hM hX (p := 0) (q := 16) rfl
  have i1 : Integrable (fun ω => M ω ^ 15 * X ω) P := by
    simpa using integrable_pow_mul_pow_of_memLp_sixteen hM hX (p := 15) (q := 1) rfl
  have i2 : Integrable (fun ω => X ω ^ 2 * M ω ^ 14) P :=
    integrable_pow_mul_pow_of_memLp_sixteen hX hM (p := 2) (q := 14) rfl
  have iS : Integrable (fun ω => (M ω + X ω) ^ 16) P := by
    have := (hM.add hX)
    simpa using integrable_pow_mul_pow_of_memLp_sixteen this hX (p := 16) (q := 0) rfl
  have hint : ∫ ω, (M ω + X ω) ^ 16 ∂P ≤ A + 983040 * (x * m ^ 7 + x ^ 8) := by
    have hH := integral_sq_mul_pow14_le hX hM
    calc ∫ ω, (M ω + X ω) ^ 16 ∂P
        ≤ ∫ ω, (M ω ^ 16 + 16 * (M ω ^ 15 * X ω) +
            983040 * (X ω ^ 2 * M ω ^ 14 + X ω ^ 16)) ∂P :=
          integral_mono iS ((iM.add (i1.const_mul 16)).add ((i2.add iX).const_mul _))
            fun ω => add_pow_sixteen_le (M ω) (X ω)
      _ = A + 16 * 0 + 983040 * ((∫ ω, X ω ^ 2 * M ω ^ 14 ∂P) + Bx) := by
          rw [integral_add (f := fun ω => M ω ^ 16 + 16 * (M ω ^ 15 * X ω))
              (g := fun ω => 983040 * (X ω ^ 2 * M ω ^ 14 + X ω ^ 16))
              (iM.add (i1.const_mul 16)) ((i2.add iX).const_mul _),
            integral_add (f := fun ω => M ω ^ 16) (g := fun ω => 16 * (M ω ^ 15 * X ω))
              iM (i1.const_mul 16), integral_const_mul, integral_const_mul,
            integral_add (f := fun ω => X ω ^ 2 * M ω ^ 14) (g := fun ω => X ω ^ 16) i2 iX, horth]
      _ ≤ A + 983040 * (x * m ^ 7 + x ^ 8) := by
          rw [sq16_pow_eight hB |>.symm] at *
          nlinarith [hH]
  refine sq16_le_of_le_pow (integral_nonneg fun ω => by positivity) (by positivity) ?_
  refine hint.trans ?_
  rw [← sq16_pow_eight hA]
  set y := 983040 * x
  have hy : 0 ≤ y := by positivity
  have hbin : m ^ 8 + 8 * m ^ 7 * y + y ^ 8 ≤ (m + y) ^ 8 := by
    nlinarith [pow_nonneg hm 6, pow_nonneg hy 6, mul_nonneg (pow_nonneg hm 6) (sq_nonneg y),
      mul_nonneg (pow_nonneg hm 2) (pow_nonneg hy 2), mul_nonneg hm hy,
      mul_nonneg (pow_nonneg hm 5) (pow_nonneg hy 3), mul_nonneg (pow_nonneg hm 4) (pow_nonneg hy 4),
      mul_nonneg (pow_nonneg hm 3) (pow_nonneg hy 5), mul_nonneg (pow_nonneg hm 2) (pow_nonneg hy 6),
      mul_nonneg hm (pow_nonneg hy 7)]
  have h8 : 983040 * x ^ 8 ≤ y ^ 8 := by
    have : x ^ 8 * 1 ≤ x ^ 8 * 983040 ^ 7 := by
      gcongr; norm_num
    calc 983040 * x ^ 8 ≤ 983040 * (x ^ 8 * 983040 ^ 7) := by nlinarith
      _ = y ^ 8 := by simp only [y]; ring
  nlinarith [mul_nonneg (pow_nonneg hm 7) hx]

/-- **Sixteenth moment of a martingale-difference sum** in squared-norm form. -/
theorem sq16_sum_le_of_orthogonal {ξ : ℕ → Ω → ℝ} (m : ℕ)
    (hLp : ∀ i < m, MemLp (ξ i) 16 P)
    (horth : ∀ j < m, ∫ ω, (∑ i ∈ Finset.range j, ξ i ω) ^ 15 * ξ j ω ∂P = 0) :
    sq16 (∫ ω, (∑ i ∈ Finset.range m, ξ i ω) ^ 16 ∂P) ≤
      983040 * ∑ i ∈ Finset.range m, sq16 (∫ ω, ξ i ω ^ 16 ∂P) := by
  induction m with
  | zero => simp [sq16]
  | succ m ih =>
    have hMLp : MemLp (fun ω => ∑ i ∈ Finset.range m, ξ i ω) 16 P := by
      have h := memLp_finsetSum' (p := 16) (μ := P) (Finset.range m) fun i hi =>
        hLp i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
      have hfun : (∑ j ∈ Finset.range m, ξ j) = fun ω => ∑ i ∈ Finset.range m, ξ i ω := by
        funext ω; simp
      rwa [hfun] at h
    have ih' := ih (fun i hi => hLp i (Nat.lt_succ_of_lt hi))
      (fun j hj => horth j (Nat.lt_succ_of_lt hj))
    have hstep := sq16_add_le hMLp (hLp m (Nat.lt_succ_self m)) (horth m (Nat.lt_succ_self m))
    simp only [Finset.sum_range_succ]
    linarith

end SignatureVolatility
