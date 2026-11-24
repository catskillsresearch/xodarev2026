module

public import SignatureVolatility.ItoCalculusKit.EighthMoment


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SignatureVolatility

/-!
# Even moments of martingale-difference sums

For `q ≥ 2` write `nrm q a = a^{1/q}`, so `nrm q (𝔼 X^{2q}) = ‖X‖_{2q}²`.
`nrm_sum_le_of_orthogonal`: if `𝔼[(∑_{i<j} ξ_i)^{2q-1} ξ_j] = 0` for every `j`, then
`‖∑_{i<m} ξ_i‖_{2q}² ≤ evenConst q ∑_{i<m} ‖ξ_i‖_{2q}²`.

The one-step estimate uses the second-order Taylor bound
`|(a+b)^{n+2} - a^{n+2} - (n+2) a^{n+1} b| ≤ ((n+2)(n+1)/2) b² (|a|+|b|)^n`, the orthogonality to
kill the linear term, and Hölder for `𝔼[X² M^{2q-2}]`.
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

/-- The constant of the even-moment inequality: `q (2q-1) 2^{2q-3}` (for `q ≥ 2`). -/
noncomputable def evenConst (q : ℕ) : ℝ := (q : ℝ) * (2 * q - 1) * 2 ^ (2 * q - 3)

lemma one_le_evenConst {q : ℕ} (hq : 2 ≤ q) : 1 ≤ evenConst q := by
  unfold evenConst
  have h1 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (1 : ℝ) ≤ 2 ^ (2 * q - 3) := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ q * (2 * q - 1) := by nlinarith
  nlinarith

/-- Pointwise `2q`-th power expansion with the linear term kept exact. -/
lemma add_pow_even_le {q : ℕ} (hq : 2 ≤ q) (a b : ℝ) :
    (a + b) ^ (2 * q) ≤ a ^ (2 * q) + 2 * q * (a ^ (2 * q - 1) * b) +
      evenConst q * (b ^ 2 * a ^ (2 * q - 2) + b ^ (2 * q)) := by
  set n := 2 * q - 2 with hn
  have h2q : 2 * q = n + 2 := by omega
  have h1 : 2 * q - 1 = n + 1 := by omega
  have h3 : 2 * q - 3 = n - 1 := by omega
  have hev : Even n := ⟨q - 1, by omega⟩
  have hqr : (2 * (q : ℝ)) = (n : ℝ) + 2 := by
    have : ((2 * q : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by rw [h2q]
    push_cast at this; linarith
  have hT : ((n : ℝ) + 2) * (n + 1) / 2 = q * (2 * q - 1) := by
    have : (n : ℝ) = 2 * q - 2 := by linarith
    rw [this]; ring
  rw [h1, h2q]
  have h := abs_add_pow_sub_taylor_le a b n
  rw [hT] at h
  have h2 : (|a| + |b|) ^ n ≤ 2 ^ (n - 1) * (|a| ^ n + |b| ^ n) :=
    add_pow_le (abs_nonneg a) (abs_nonneg b) n
  rw [hev.pow_abs, hev.pow_abs] at h2
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hq0 : (0 : ℝ) ≤ q * (2 * q - 1) := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have h4 := (abs_le.mp h).2
  have h5 : q * (2 * q - 1) * b ^ 2 * (|a| + |b|) ^ n ≤
      q * (2 * q - 1) * (b ^ 2 * (2 ^ (n - 1) * (a ^ n + b ^ n))) := by
    rw [mul_assoc]; gcongr
  have e : b ^ 2 * b ^ n = b ^ (n + 2) := by ring
  have e3 : q * (2 * q - 1) * (b ^ 2 * (2 ^ (n - 1) * (a ^ n + b ^ n))) =
      evenConst q * (b ^ 2 * a ^ n + b ^ (n + 2)) := by
    unfold evenConst; rw [h3, ← e]; ring
  have e2 : 2 * (q : ℝ) * (a ^ (n + 1) * b) = (n + 2) * a ^ (n + 1) * b := by
    rw [hqr]; ring
  rw [e2]
  linarith [h4, h5, e3]

private lemma abs_pow_mul_pow_le_even {N : ℕ} (hN : Even N) (a b : ℝ) {p r : ℕ} (h : p + r = N) :
    |a ^ p * b ^ r| ≤ a ^ N + b ^ N := by
  rw [abs_mul, abs_pow, abs_pow]
  have ha8 : |a| ^ N = a ^ N := hN.pow_abs a
  have hb8 : |b| ^ N = b ^ N := hN.pow_abs b
  have ha0 : 0 ≤ a ^ N := hN.pow_nonneg a
  have hb0 : 0 ≤ b ^ N := hN.pow_nonneg b
  rcases le_total |a| |b| with hab | hab
  · calc |a| ^ p * |b| ^ r ≤ |b| ^ p * |b| ^ r := by gcongr
      _ = |b| ^ N := by rw [← pow_add, h]
      _ ≤ a ^ N + b ^ N := by rw [hb8]; linarith
  · calc |a| ^ p * |b| ^ r ≤ |a| ^ p * |a| ^ r := by gcongr
      _ = |a| ^ N := by rw [← pow_add, h]
      _ ≤ a ^ N + b ^ N := by rw [ha8]; linarith

omit [IsProbabilityMeasure P] in
/-- Mixed monomials of total even degree `N` of two `L^N` variables are integrable. -/
lemma integrable_pow_mul_pow_of_memLp_even [IsFiniteMeasure P] {N : ℕ} (hN : Even N)
    {f g : Ω → ℝ} (hf : MemLp f N P) (hg : MemLp g N P) {p r : ℕ} (h : p + r = N) :
    Integrable (fun ω => f ω ^ p * g ω ^ r) P := by
  have hf8 : Integrable (fun ω => ‖f ω‖ ^ N) P := hf.integrable_norm_pow'
  have hg8 : Integrable (fun ω => ‖g ω‖ ^ N) P := hg.integrable_norm_pow'
  refine Integrable.mono' (hf8.fun_add hg8)
    ((hf.aestronglyMeasurable.pow p).mul (hg.aestronglyMeasurable.pow r))
    (ae_of_all _ fun ω => ?_)
  have h1 := abs_pow_mul_pow_le_even hN (f ω) (g ω) h
  simp only [Real.norm_eq_abs, hN.pow_abs]
  exact h1

omit [IsProbabilityMeasure P] in
lemma integrable_pow_of_memLp_evenDeg [IsFiniteMeasure P] {N : ℕ} (hN : Even N) {f : Ω → ℝ}
    (hf : MemLp f N P) : Integrable (fun ω => f ω ^ N) P := by
  simpa using integrable_pow_mul_pow_of_memLp_even hN hf hf (p := N) (r := 0) (by simp)

/-- `a ↦ a^{1/q}`: the squared `L^{2q}` norm from the `2q`-th moment. -/
noncomputable def nrm (q : ℕ) (a : ℝ) : ℝ := a ^ (1 / (q : ℝ))

lemma nrm_nonneg (q : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ nrm q a := Real.rpow_nonneg ha _

lemma nrm_pow {q : ℕ} (hq : q ≠ 0) {a : ℝ} (ha : 0 ≤ a) : nrm q a ^ q = a := by
  unfold nrm
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha, one_div_mul_cancel (by exact_mod_cast hq),
    Real.rpow_one]

lemma nrm_pow_self {q : ℕ} (hq : q ≠ 0) {x : ℝ} (hx : 0 ≤ x) : nrm q (x ^ q) = x := by
  unfold nrm
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_one_div_cancel (by exact_mod_cast hq),
    Real.rpow_one]

lemma nrm_mul (q : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    nrm q (x * y) = nrm q x * nrm q y := by
  unfold nrm; exact Real.mul_rpow hx hy

lemma nrm_mono {q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : nrm q a ≤ nrm q b := by
  unfold nrm; exact Real.rpow_le_rpow ha hab (by positivity)

lemma nrm_zero (q : ℕ) (hq : q ≠ 0) : nrm q 0 = 0 := by
  unfold nrm; exact Real.zero_rpow (by positivity)

lemma nrm_le_of_le_pow {q : ℕ} (hq : q ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ b ^ q) : nrm q a ≤ b :=
  (nrm_mono ha h).trans (nrm_pow_self hq hb).le

omit [IsProbabilityMeasure P] in
/-- Hölder: `𝔼[X² M^{2q-2}] ≤ ‖X‖_{2q}² ‖M‖_{2q}^{2q-2}`. -/
lemma integral_sq_mul_pow_le {q : ℕ} (hq : 2 ≤ q) {X M : Ω → ℝ} (hX : MemLp X (2 * q : ℕ) P)
    (hM : MemLp M (2 * q : ℕ) P) :
    ∫ ω, X ω ^ 2 * M ω ^ (2 * q - 2) ∂P ≤
      nrm q (∫ ω, X ω ^ (2 * q) ∂P) * nrm q (∫ ω, M ω ^ (2 * q) ∂P) ^ (q - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hqm : (0 : ℝ) < q - 1 := by linarith
  have hpq : (q : ℝ).HolderConjugate (q / (q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hq1).mpr rfl
  have hcast : ∀ m : ℕ, ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal m := fun m => by simp
  have hf : MemLp (fun ω => X ω ^ 2) (ENNReal.ofReal q) P := by
    have h := hX.norm_rpow_div 2
    have e1 : ((2 * q : ℕ) : ℝ≥0∞) / 2 = ENNReal.ofReal q := by
      rw [hcast, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_div_of_pos (by norm_num)]
      congr 1; push_cast; ring
    rw [e1] at h
    refine h.congr_norm (hX.aestronglyMeasurable.pow 2) (ae_of_all _ fun ω => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  have hg : MemLp (fun ω => (M ω ^ 2) ^ (q - 1)) (ENNReal.ofReal (q / (q - 1))) P := by
    have h := hM.norm_rpow_div ((2 * (q - 1) : ℕ) : ℝ≥0∞)
    have e1 : ((2 * q : ℕ) : ℝ≥0∞) / ((2 * (q - 1) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (q / (q - 1)) := by
      rw [hcast, hcast, ← ENNReal.ofReal_div_of_pos (by
        have : (1 : ℕ) ≤ q - 1 := by omega
        have : (1 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast; linarith)]
      congr 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      field_simp
    rw [e1] at h
    refine h.congr_norm ((hM.aestronglyMeasurable.pow 2).pow _) (ae_of_all _ fun ω => ?_)
    rw [ENNReal.toReal_natCast, Real.rpow_natCast, norm_pow, norm_norm, norm_pow, norm_pow,
      ← pow_mul]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun ω => sq_nonneg (X ω))
    (ae_of_all _ fun ω => by positivity) hf hg
  have e1 : ∀ ω, (X ω ^ 2) ^ (q : ℝ) = X ω ^ (2 * q) := fun ω => by
    rw [Real.rpow_natCast, ← pow_mul]
  have e2 : ∀ ω, ((M ω ^ 2) ^ (q - 1)) ^ ((q : ℝ) / (q - 1)) = M ω ^ (2 * q) := fun ω => by
    rw [← Real.rpow_natCast (M ω ^ 2) (q - 1), ← Real.rpow_mul (sq_nonneg _),
      Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one,
      mul_div_cancel₀ _ hqm.ne', Real.rpow_natCast, ← pow_mul]
  simp only [e1, e2] at h
  have hA : 0 ≤ ∫ ω, M ω ^ (2 * q) ∂P :=
    integral_nonneg fun ω => Even.pow_nonneg ⟨q, by ring⟩ _
  have e3 : (∫ ω, M ω ^ (2 * q) ∂P) ^ (1 / ((q : ℝ) / (q - 1))) =
      nrm q (∫ ω, M ω ^ (2 * q) ∂P) ^ (q - 1) := by
    unfold nrm
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    congr 1; field_simp
  have e4 : (∫ ω, X ω ^ 2 * (M ω ^ 2) ^ (q - 1) ∂P) = ∫ ω, X ω ^ 2 * M ω ^ (2 * q - 2) ∂P := by
    congr 1; funext ω; rw [← pow_mul]; congr 2; omega
  rw [e3, e4] at h
  exact h

/-- `(a + b)^q ≥ a^q + q a^{q-1} b + b^q` for `a, b ≥ 0`, `q ≥ 2`. -/
lemma add_pow_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    a ^ (q + 2) + (q + 2) * a ^ (q + 1) * b + b ^ (q + 2) ≤ (a + b) ^ (q + 2) := by
  induction q with
  | zero => norm_num; nlinarith [mul_nonneg ha hb]
  | succ q ih =>
    have hab : 0 ≤ a + b := by positivity
    have h1 := mul_le_mul_of_nonneg_left ih hab
    have e : (a + b) ^ (q + 1 + 2) = (a + b) * (a + b) ^ (q + 2) := by ring
    rw [e]
    refine le_trans ?_ h1
    have e1 : (a + b) * (a ^ (q + 2) + (q + 2) * a ^ (q + 1) * b + b ^ (q + 2)) =
        a ^ (q + 1 + 2) + ((↑(q + 1) : ℝ) + 2) * a ^ (q + 1 + 1) * b + b ^ (q + 1 + 2) +
          (a * b ^ (q + 2) + (q + 2) * a ^ (q + 1) * b ^ 2) := by push_cast; ring
    rw [e1]
    have : 0 ≤ a * b ^ (q + 2) := by positivity
    have : 0 ≤ (q + 2) * a ^ (q + 1) * b ^ 2 := by positivity
    linarith

/-- One martingale step in squared `L^{2q}` norm. -/
lemma nrm_add_le {q : ℕ} (hq : 2 ≤ q) {M X : Ω → ℝ} (hM : MemLp M (2 * q : ℕ) P)
    (hX : MemLp X (2 * q : ℕ) P) (horth : ∫ ω, M ω ^ (2 * q - 1) * X ω ∂P = 0) :
    nrm q (∫ ω, (M ω + X ω) ^ (2 * q) ∂P) ≤
      nrm q (∫ ω, M ω ^ (2 * q) ∂P) + evenConst q * nrm q (∫ ω, X ω ^ (2 * q) ∂P) := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hq0 : q ≠ 0 := by omega
  set A := ∫ ω, M ω ^ (2 * q) ∂P
  set Bx := ∫ ω, X ω ^ (2 * q) ∂P
  have hA : 0 ≤ A := integral_nonneg fun ω => hev.pow_nonneg _
  have hB : 0 ≤ Bx := integral_nonneg fun ω => hev.pow_nonneg _
  set m := nrm q A
  set x := nrm q Bx
  have hm : 0 ≤ m := nrm_nonneg q hA
  have hx : 0 ≤ x := nrm_nonneg q hB
  have hK := one_le_evenConst hq
  set K := evenConst q
  have iM : Integrable (fun ω => M ω ^ (2 * q)) P := integrable_pow_of_memLp_evenDeg hev hM
  have iX : Integrable (fun ω => X ω ^ (2 * q)) P := integrable_pow_of_memLp_evenDeg hev hX
  have i1 : Integrable (fun ω => M ω ^ (2 * q - 1) * X ω) P := by
    simpa using integrable_pow_mul_pow_of_memLp_even hev hM hX (p := 2 * q - 1) (r := 1)
      (by omega)
  have i2 : Integrable (fun ω => X ω ^ 2 * M ω ^ (2 * q - 2)) P :=
    integrable_pow_mul_pow_of_memLp_even hev hX hM (p := 2) (r := 2 * q - 2) (by omega)
  have iS : Integrable (fun ω => (M ω + X ω) ^ (2 * q)) P :=
    integrable_pow_of_memLp_evenDeg hev (hM.add hX)
  have hH := integral_sq_mul_pow_le hq hX hM
  have hint : ∫ ω, (M ω + X ω) ^ (2 * q) ∂P ≤ m ^ q + K * (x * m ^ (q - 1) + x ^ q) := by
    calc ∫ ω, (M ω + X ω) ^ (2 * q) ∂P
        ≤ ∫ ω, (M ω ^ (2 * q) + 2 * q * (M ω ^ (2 * q - 1) * X ω) +
            K * (X ω ^ 2 * M ω ^ (2 * q - 2) + X ω ^ (2 * q))) ∂P :=
          integral_mono iS ((iM.add (i1.const_mul _)).add ((i2.add iX).const_mul _))
            fun ω => add_pow_even_le hq (M ω) (X ω)
      _ = A + 2 * q * 0 + K * ((∫ ω, X ω ^ 2 * M ω ^ (2 * q - 2) ∂P) + Bx) := by
          rw [integral_add (f := fun ω => M ω ^ (2 * q) + 2 * q * (M ω ^ (2 * q - 1) * X ω))
              (g := fun ω => K * (X ω ^ 2 * M ω ^ (2 * q - 2) + X ω ^ (2 * q)))
              (iM.add (i1.const_mul _)) ((i2.add iX).const_mul _),
            integral_add (f := fun ω => M ω ^ (2 * q))
              (g := fun ω => 2 * q * (M ω ^ (2 * q - 1) * X ω)) iM (i1.const_mul _),
            integral_const_mul, integral_const_mul,
            integral_add (f := fun ω => X ω ^ 2 * M ω ^ (2 * q - 2)) (g := fun ω => X ω ^ (2 * q))
              i2 iX, horth]
      _ ≤ m ^ q + K * (x * m ^ (q - 1) + x ^ q) := by
          rw [nrm_pow hq0 hA, nrm_pow hq0 hB]
          have : 0 ≤ K := by linarith
          nlinarith [hH]
  refine nrm_le_of_le_pow hq0 (integral_nonneg fun ω => hev.pow_nonneg _) (by positivity) ?_
  refine hint.trans ?_
  set y := K * x
  have hy : 0 ≤ y := by positivity
  obtain ⟨r, hr⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hbin := add_pow_ge hm hy r
  rw [← hr] at hbin
  have hq1 : q - 1 = r + 1 := by omega
  rw [hq1]
  have hxq : K * x ^ q ≤ y ^ q := by
    have h1 : K ≤ K ^ q := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ q := pow_le_pow_right₀ hK (by omega)
    calc K * x ^ q ≤ K ^ q * x ^ q := by gcongr
      _ = y ^ q := by simp only [y]; ring
  have hlin : K * (x * m ^ (r + 1)) ≤ (r + 2 : ℝ) * m ^ (r + 1) * y := by
    have : 0 ≤ x * m ^ (r + 1) * K := by positivity
    simp only [y]; nlinarith
  nlinarith [hbin, hxq, hlin]

/-- **Even moments of a martingale-difference sum** in squared-norm form. -/
theorem nrm_sum_le_of_orthogonal {q : ℕ} (hq : 2 ≤ q) {ξ : ℕ → Ω → ℝ} (m : ℕ)
    (hLp : ∀ i < m, MemLp (ξ i) (2 * q : ℕ) P)
    (horth : ∀ j < m, ∫ ω, (∑ i ∈ Finset.range j, ξ i ω) ^ (2 * q - 1) * ξ j ω ∂P = 0) :
    nrm q (∫ ω, (∑ i ∈ Finset.range m, ξ i ω) ^ (2 * q) ∂P) ≤
      evenConst q * ∑ i ∈ Finset.range m, nrm q (∫ ω, ξ i ω ^ (2 * q) ∂P) := by
  induction m with
  | zero => simp [nrm_zero q (by omega : q ≠ 0), zero_pow (by omega : 2 * q ≠ 0)]
  | succ m ih =>
    have hMLp : MemLp (fun ω => ∑ i ∈ Finset.range m, ξ i ω) (2 * q : ℕ) P := by
      have h := memLp_finsetSum' (p := ((2 * q : ℕ) : ℝ≥0∞)) (μ := P) (Finset.range m)
        fun i hi => hLp i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
      have hfun : (∑ j ∈ Finset.range m, ξ j) = fun ω => ∑ i ∈ Finset.range m, ξ i ω := by
        funext ω; simp
      rwa [hfun] at h
    have ih' := ih (fun i hi => hLp i (Nat.lt_succ_of_lt hi))
      (fun j hj => horth j (Nat.lt_succ_of_lt hj))
    have hstep := nrm_add_le hq hMLp (hLp m (Nat.lt_succ_self m))
      (horth m (Nat.lt_succ_self m))
    simp only [Finset.sum_range_succ]
    linarith

end SignatureVolatility
