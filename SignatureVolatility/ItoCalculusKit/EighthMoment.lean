module

public import SignatureVolatility.ItoCalculusKit.FourthMoment


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SignatureVolatility

/-!
# Eighth moments of martingale-difference sums

`integral_sum_pow_eight_le_of_orthogonal`: if `𝔼[(∑_{i<j} ξ_i)⁷ ξ_j] = 0` for every `j`, then
`𝔼[(∑_{i<m} ξ_i)⁸] ≤ (14 ∑_{i<m} ‖ξ_i‖₈²)⁴`, with `‖ξ‖₈² = (𝔼 ξ⁸)^{1/4}`. The odd mixed terms are
absorbed by AM–GM, the even ones by a Hölder inequality for nonnegative variables proved by
normalised AM–GM (`integral_pow_mul_pow_le_root`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(𝔼 f⁴)^{1/4}` written with square roots. -/
noncomputable def root4 (a : ℝ) : ℝ := Real.sqrt (Real.sqrt a)

lemma root4_nonneg (a : ℝ) : 0 ≤ root4 a := Real.sqrt_nonneg _

lemma root4_pow_four {a : ℝ} (ha : 0 ≤ a) : root4 a ^ 4 = a := by
  unfold root4
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt ha]

lemma root4_le_of_le_pow {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 4) : root4 a ≤ b := by
  unfold root4
  refine Real.sqrt_le_iff.mpr ⟨hb, Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩⟩
  calc a ≤ b ^ 4 := h
    _ = (b ^ 2) ^ 2 := by ring

lemma amgm_four {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p q : ℕ} (h : p + q = 4) :
    x ^ p * y ^ q ≤ ((p : ℝ) * x ^ 4 + (q : ℝ) * y ^ 4) / 4 := by
  have hp : p ≤ 4 := by omega
  obtain rfl : q = 4 - p := by omega
  interval_cases p
  · simp
  · norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - y)) (by positivity : 0 ≤ x ^ 2 + 2 * x * y + 3 * y ^ 2)]
  · norm_num
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  · norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - y)) (by positivity : 0 ≤ 3 * x ^ 2 + 2 * x * y + y ^ 2)]
  · simp

omit [IsProbabilityMeasure P] in
/-- **Hölder for nonnegative variables** (`p + q = 4`, both positive):
`𝔼[X^p Y^q] ≤ (𝔼X⁴)^{p/4} (𝔼Y⁴)^{q/4}`. -/
lemma integral_pow_mul_pow_le_root {X Y : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω)
    (hX4 : Integrable (fun ω => X ω ^ 4) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    {p q : ℕ} (hpq : p + q = 4) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hXY : Integrable (fun ω => X ω ^ p * Y ω ^ q) P) :
    ∫ ω, X ω ^ p * Y ω ^ q ∂P ≤
      root4 (∫ ω, X ω ^ 4 ∂P) ^ p * root4 (∫ ω, Y ω ^ 4 ∂P) ^ q := by
  set a := ∫ ω, X ω ^ 4 ∂P with ha
  set b := ∫ ω, Y ω ^ 4 ∂P with hb
  have ha0 : 0 ≤ a := integral_nonneg fun ω => by positivity
  have hb0 : 0 ≤ b := integral_nonneg fun ω => by positivity
  have hR : 0 ≤ root4 a ^ p * root4 b ^ q := by
    have := root4_nonneg a; have := root4_nonneg b; positivity
  by_cases hazero : a = 0
  · have hae := (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hX4).mp hazero
    have : ∫ ω, X ω ^ p * Y ω ^ q ∂P = 0 := by
      refine integral_eq_zero_of_ae (hae.mono fun ω hω => ?_)
      simp only [Pi.zero_apply] at hω
      have hx : X ω = 0 := by
        have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp hω; exact this
      simp [hx, zero_pow (by omega : p ≠ 0)]
    rw [this]; exact hR
  by_cases hbzero : b = 0
  · have hae := (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hY4).mp hbzero
    have : ∫ ω, X ω ^ p * Y ω ^ q ∂P = 0 := by
      refine integral_eq_zero_of_ae (hae.mono fun ω hω => ?_)
      simp only [Pi.zero_apply] at hω
      have hy : Y ω = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp hω
      simp [hy, zero_pow (by omega : q ≠ 0)]
    rw [this]; exact hR
  set ra := root4 a with hra
  set rb := root4 b with hrb
  have hra4 : ra ^ 4 = a := root4_pow_four ha0
  have hrb4 : rb ^ 4 = b := root4_pow_four hb0
  have hrapos : 0 < ra := by
    rcases (show 0 ≤ ra from root4_nonneg a).eq_or_lt with h | h
    · exfalso; apply hazero; rw [← hra4, ← h]; simp
    · exact h
  have hrbpos : 0 < rb := by
    rcases (show 0 ≤ rb from root4_nonneg b).eq_or_lt with h | h
    · exfalso; apply hbzero; rw [← hrb4, ← h]; simp
    · exact h
  set C1 : ℝ := ra ^ p * rb ^ q * (p : ℝ) / (4 * ra ^ 4) with hC1
  set C2 : ℝ := ra ^ p * rb ^ q * (q : ℝ) / (4 * rb ^ 4) with hC2
  have hpt : ∀ ω, X ω ^ p * Y ω ^ q ≤ C1 * X ω ^ 4 + C2 * Y ω ^ 4 := by
    intro ω
    have h := amgm_four (div_nonneg (hX ω) hrapos.le) (div_nonneg (hY ω) hrbpos.le) hpq
    rw [div_pow, div_pow, div_pow, div_pow] at h
    have hk : X ω ^ p * Y ω ^ q = ra ^ p * rb ^ q * (X ω ^ p / ra ^ p * (Y ω ^ q / rb ^ q)) := by
      field_simp
    rw [hk]
    calc ra ^ p * rb ^ q * (X ω ^ p / ra ^ p * (Y ω ^ q / rb ^ q))
        ≤ ra ^ p * rb ^ q * (((p : ℝ) * (X ω ^ 4 / ra ^ 4) + (q : ℝ) * (Y ω ^ 4 / rb ^ 4)) / 4) :=
          mul_le_mul_of_nonneg_left h hR
      _ = C1 * X ω ^ 4 + C2 * Y ω ^ 4 := by
          rw [hC1, hC2]; field_simp
  calc ∫ ω, X ω ^ p * Y ω ^ q ∂P ≤ ∫ ω, (C1 * X ω ^ 4 + C2 * Y ω ^ 4) ∂P :=
        integral_mono hXY ((hX4.const_mul C1).add (hY4.const_mul C2)) hpt
    _ = C1 * a + C2 * b := by
        rw [integral_add (hX4.const_mul C1) (hY4.const_mul C2), integral_const_mul,
          integral_const_mul]
    _ = ra ^ p * rb ^ q := by
        rw [hC1, hC2, ← hra4, ← hrb4]
        have hpq' : (p : ℝ) + (q : ℝ) = 4 := by exact_mod_cast hpq
        field_simp
        linear_combination hpq'

private lemma abs_pow_mul_pow_le_eight (a b : ℝ) {p q : ℕ} (h : p + q = 8) :
    |a ^ p * b ^ q| ≤ a ^ 8 + b ^ 8 := by
  rw [abs_mul, abs_pow, abs_pow]
  have ha8 : |a| ^ 8 = a ^ 8 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have hb8 : |b| ^ 8 = b ^ 8 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have ha0 : 0 ≤ a ^ 8 := by positivity
  have hb0 : 0 ≤ b ^ 8 := by positivity
  rcases le_total |a| |b| with hab | hab
  · calc |a| ^ p * |b| ^ q ≤ |b| ^ p * |b| ^ q := by gcongr
      _ = |b| ^ 8 := by rw [← pow_add, h]
      _ ≤ a ^ 8 + b ^ 8 := by rw [hb8]; linarith
  · calc |a| ^ p * |b| ^ q ≤ |a| ^ p * |a| ^ q := by gcongr
      _ = |a| ^ 8 := by rw [← pow_add, h]
      _ ≤ a ^ 8 + b ^ 8 := by rw [ha8]; linarith

/-- Powers up to the eighth of an `L⁸` variable are integrable. -/
lemma integrable_pow_of_memLp_eight {f : Ω → ℝ} (hf : MemLp f 8 P) {k : ℕ} (hk : k ≤ 8) :
    Integrable (fun ω => f ω ^ k) P := by
  have h1 : MemLp f (k : ℝ≥0∞) P := hf.mono_exponent (by exact_mod_cast hk)
  have h2 : Integrable (fun ω => ‖f ω‖ ^ k) P := h1.integrable_norm_pow'
  refine (integrable_norm_iff (hf.aestronglyMeasurable.pow k)).mp ?_
  simpa [norm_pow] using h2

omit [IsProbabilityMeasure P] in
/-- Mixed eighth-order monomials of two `L⁸` variables are integrable. -/
lemma integrable_pow_mul_pow_of_memLp_eight [IsFiniteMeasure P] {f g : Ω → ℝ}
    (hf : MemLp f 8 P) (hg : MemLp g 8 P) {p q : ℕ} (h : p + q = 8) :
    Integrable (fun ω => f ω ^ p * g ω ^ q) P := by
  have hf8 : Integrable (fun ω => ‖f ω‖ ^ 8) P := by
    simpa using (hf.integrable_norm_pow' (p := 8))
  have hg8 : Integrable (fun ω => ‖g ω‖ ^ 8) P := by
    simpa using (hg.integrable_norm_pow' (p := 8))
  refine Integrable.mono' (hf8.fun_add hg8)
    ((hf.aestronglyMeasurable.pow p).mul (hg.aestronglyMeasurable.pow q))
    (ae_of_all _ fun ω => ?_)
  have h1 := abs_pow_mul_pow_le_eight (f ω) (g ω) h
  have e1 : ‖f ω‖ ^ 8 = f ω ^ 8 := by
    rw [Real.norm_eq_abs, ← abs_pow]; exact abs_of_nonneg (by positivity)
  have e2 : ‖g ω‖ ^ 8 = g ω ^ 8 := by
    rw [Real.norm_eq_abs, ← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [e1, e2]
  simpa [Real.norm_eq_abs] using h1

omit [IsProbabilityMeasure P] in
/-- Hölder for even monomials of `L⁸` variables:
`𝔼[f^{2p} g^{2q}] ≤ ‖f‖₈^{2p} ‖g‖₈^{2q}` for `p + q = 4`, `p, q ≥ 1`. -/
lemma integral_pow_mul_pow_le_root_eight [IsFiniteMeasure P] {f g : Ω → ℝ}
    (hf : MemLp f 8 P) (hg : MemLp g 8 P) {p q : ℕ} (hpq : p + q = 4) (hp : 1 ≤ p)
    (hq : 1 ≤ q) :
    ∫ ω, f ω ^ (2 * p) * g ω ^ (2 * q) ∂P ≤
      root4 (∫ ω, f ω ^ 8 ∂P) ^ p * root4 (∫ ω, g ω ^ 8 ∂P) ^ q := by
  have e8 : ∀ h : Ω → ℝ, (fun ω => (h ω ^ 2) ^ 4) = fun ω => h ω ^ 8 := fun h => by
    funext ω; ring
  have hf8 := (integrable_pow_mul_pow_of_memLp_eight hf hg (p := 8) (q := 0) rfl).congr
    (ae_of_all _ fun ω => by simp only [pow_zero, mul_one]; ring : ∀ᵐ ω ∂P, f ω ^ 8 * g ω ^ 0 = (f ω ^ 2) ^ 4)
  have hg8 := (integrable_pow_mul_pow_of_memLp_eight hf hg (p := 0) (q := 8) rfl).congr
    (ae_of_all _ fun ω => by simp only [pow_zero, one_mul]; ring : ∀ᵐ ω ∂P, f ω ^ 0 * g ω ^ 8 = (g ω ^ 2) ^ 4)
  have hJ := (integrable_pow_mul_pow_of_memLp_eight hf hg (p := 2 * p) (q := 2 * q)
    (by omega)).congr (ae_of_all _ fun ω => by simp only [pow_mul] :
      ∀ᵐ ω ∂P, f ω ^ (2 * p) * g ω ^ (2 * q) = (f ω ^ 2) ^ p * (g ω ^ 2) ^ q)
  have h := integral_pow_mul_pow_le_root (P := P) (X := fun ω => f ω ^ 2) (Y := fun ω => g ω ^ 2)
    (fun ω => sq_nonneg _) (fun ω => sq_nonneg _) hf8 hg8 hpq hp hq hJ
  simp only [← pow_mul] at h
  simpa only [mul_comm 2 p, mul_comm 2 q] using h

/-- The degree-eight binomial with its odd interior terms absorbed by AM–GM. -/
lemma add_pow_eight_le (m x : ℝ) :
    (m + x) ^ 8 ≤ m ^ 8 + 8 * (m ^ 7 * x) + 56 * (m ^ 6 * x ^ 2) + 126 * (m ^ 4 * x ^ 4) +
      60 * (m ^ 2 * x ^ 6) + 5 * x ^ 8 := by
  have e1 : 2 * (m ^ 5 * x ^ 3) ≤ m ^ 6 * x ^ 2 + m ^ 4 * x ^ 4 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ m ^ 4 * x ^ 2) (sq_nonneg (m - x))]
  have e2 : 2 * (m ^ 3 * x ^ 5) ≤ m ^ 4 * x ^ 4 + m ^ 2 * x ^ 6 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ m ^ 2 * x ^ 4) (sq_nonneg (m - x))]
  have e3 : 2 * (m * x ^ 7) ≤ m ^ 2 * x ^ 6 + x ^ 8 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 6) (sq_nonneg (m - x))]
  have hexp : (m + x) ^ 8 = m ^ 8 + 8 * (m ^ 7 * x) + 28 * (m ^ 6 * x ^ 2) +
      56 * (m ^ 5 * x ^ 3) + 70 * (m ^ 4 * x ^ 4) + 56 * (m ^ 3 * x ^ 5) +
      28 * (m ^ 2 * x ^ 6) + 8 * (m * x ^ 7) + x ^ 8 := by ring
  rw [hexp]; linarith

/-- **Eighth moment of a martingale-difference sum.** -/
theorem integral_sum_pow_eight_le_of_orthogonal {ξ : ℕ → Ω → ℝ} (m : ℕ)
    (hLp : ∀ i < m, MemLp (ξ i) 8 P)
    (horth : ∀ j < m, ∫ ω, (∑ i ∈ Finset.range j, ξ i ω) ^ 7 * ξ j ω ∂P = 0) :
    ∫ ω, (∑ i ∈ Finset.range m, ξ i ω) ^ 8 ∂P ≤
      (14 * ∑ i ∈ Finset.range m, root4 (∫ ω, ξ i ω ^ 8 ∂P)) ^ 4 := by
  induction m with
  | zero => simp
  | succ m ih =>
    set M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, ξ i ω with hM
    set X : Ω → ℝ := ξ m with hX
    set S : ℝ := ∑ i ∈ Finset.range m, root4 (∫ ω, ξ i ω ^ 8 ∂P) with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => root4_nonneg _
    have hMLp : MemLp M 8 P := by
      have h := memLp_finsetSum' (p := 8) (μ := P) (Finset.range m) fun i hi =>
        hLp i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
      have hfun : (∑ j ∈ Finset.range m, ξ j) = M := by funext ω; simp [M]
      rwa [hfun] at h
    have hXLp : MemLp X 8 P := hLp m (Nat.lt_succ_self m)
    have ih' := ih (fun i hi => hLp i (Nat.lt_succ_of_lt hi))
      (fun j hj => horth j (Nat.lt_succ_of_lt hj))
    have I80 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 8) (q := 0) rfl
    have I71 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 7) (q := 1) rfl
    have I62 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 6) (q := 2) rfl
    have I44 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 4) (q := 4) rfl
    have I26 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 2) (q := 6) rfl
    have I08 := integrable_pow_mul_pow_of_memLp_eight hMLp hXLp (p := 0) (q := 8) rfl
    simp only [pow_zero, mul_one, one_mul, pow_one] at I80 I71 I08
    have hsum : ∀ ω, (∑ i ∈ Finset.range (m + 1), ξ i ω) = M ω + X ω := fun ω => by
      rw [Finset.sum_range_succ]
    set a := ∫ ω, M ω ^ 8 ∂P with ha
    set c := ∫ ω, X ω ^ 8 ∂P with hc
    have ha0 : 0 ≤ a := integral_nonneg fun ω => by positivity
    have hc0 : 0 ≤ c := integral_nonneg fun ω => by positivity
    set ra := root4 a with hra
    set rc := root4 c with hrc
    have hra0 : 0 ≤ ra := root4_nonneg a
    have hrc0 : 0 ≤ rc := root4_nonneg c
    have hra4 : ra ^ 4 = a := root4_pow_four ha0
    have hrc4 : rc ^ 4 = c := root4_pow_four hc0
    have h62 : ∫ ω, M ω ^ 6 * X ω ^ 2 ∂P ≤ ra ^ 3 * rc ^ 1 :=
      integral_pow_mul_pow_le_root_eight hMLp hXLp (p := 3) (q := 1) rfl (by norm_num) le_rfl
    have h44 : ∫ ω, M ω ^ 4 * X ω ^ 4 ∂P ≤ ra ^ 2 * rc ^ 2 :=
      integral_pow_mul_pow_le_root_eight hMLp hXLp (p := 2) (q := 2) rfl (by norm_num)
        (by norm_num)
    have h26 : ∫ ω, M ω ^ 2 * X ω ^ 6 ∂P ≤ ra ^ 1 * rc ^ 3 :=
      integral_pow_mul_pow_le_root_eight hMLp hXLp (p := 1) (q := 3) rfl le_rfl (by norm_num)
    have hbound : ∫ ω, (∑ i ∈ Finset.range (m + 1), ξ i ω) ^ 8 ∂P ≤
        a + 8 * 0 + 56 * ∫ ω, M ω ^ 6 * X ω ^ 2 ∂P + 126 * ∫ ω, M ω ^ 4 * X ω ^ 4 ∂P +
          60 * ∫ ω, M ω ^ 2 * X ω ^ 6 ∂P + 5 * c := by
      have J1 := I80.fun_add (I71.const_mul 8)
      have J2 := J1.fun_add (I62.const_mul 56)
      have J3 := J2.fun_add (I44.const_mul 126)
      have J4 := J3.fun_add (I26.const_mul 60)
      have hint := J4.fun_add (I08.const_mul 5)
      have hLHS : Integrable (fun ω => (∑ i ∈ Finset.range (m + 1), ξ i ω) ^ 8) P := by
        simp_rw [hsum]
        exact (integrable_pow_mul_pow_of_memLp_eight (hMLp.add hXLp) hXLp (p := 8) (q := 0)
          rfl).congr (ae_of_all _ fun ω => by simp)
      refine (integral_mono hLHS hint fun ω => ?_).trans (le_of_eq ?_)
      · simp only; rw [hsum]; exact add_pow_eight_le _ _
      · have h7 : ∫ ω, M ω ^ 7 * X ω ∂P = 0 := horth m (Nat.lt_succ_self m)
        rw [integral_add J4 (I08.const_mul 5), integral_add J3 (I26.const_mul 60),
          integral_add J2 (I44.const_mul 126), integral_add J1 (I62.const_mul 56),
          integral_add I80 (I71.const_mul 8), integral_const_mul, integral_const_mul,
          integral_const_mul, integral_const_mul, integral_const_mul, h7]
    refine hbound.trans ?_
    have hra : ra ≤ 14 * S := root4_le_of_le_pow (by positivity) ih'
    rw [Finset.sum_range_succ, ← hrc]
    calc a + 8 * 0 + 56 * ∫ ω, M ω ^ 6 * X ω ^ 2 ∂P + 126 * ∫ ω, M ω ^ 4 * X ω ^ 4 ∂P +
          60 * ∫ ω, M ω ^ 2 * X ω ^ 6 ∂P + 5 * c
        ≤ ra ^ 4 + 56 * (ra ^ 3 * rc) + 126 * (ra ^ 2 * rc ^ 2) + 60 * (ra * rc ^ 3) +
            5 * rc ^ 4 := by
          rw [hra4, hrc4]; simp only [pow_one] at h62 h26; linarith
      _ ≤ (ra + 14 * rc) ^ 4 := by
          nlinarith [pow_nonneg hra0 3, pow_nonneg hrc0 3, mul_nonneg (pow_nonneg hra0 2)
            (pow_nonneg hrc0 2), mul_nonneg hra0 (pow_nonneg hrc0 3), pow_nonneg hrc0 4,
            mul_nonneg (pow_nonneg hra0 3) hrc0]
      _ ≤ (14 * (S + rc)) ^ 4 := by
          apply pow_le_pow_left₀ (by positivity); linarith

end SignatureVolatility
