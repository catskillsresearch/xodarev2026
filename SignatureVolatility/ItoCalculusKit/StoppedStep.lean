module

public import SignatureVolatility.ItoCalculusKit.StoppedRaw

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# One step of the weighted energy estimate

Abstract form of one grid step of `Φ(t) = E[I_t² e^{-Q_t}]` for the difference `I` of two
solutions of the linear equation `dI = I σ dW`, with `Q = ∫ σ²`. With `a = e^{-Q_u} ∈ [0, 1]`,
`ΔQ = Q_v - Q_u`, `G = I_u σ_u` and a step of length `s²`:
`E[I_v² a e^{-ΔQ}] - E[I_u² a] ≤ C₃ s³ + C₄ s⁴`. The `E[a G² ΔW²] = s² E[a I_u² σ_u²]` terms
cancel; all other terms are `O(s³)` by Cauchy–Schwarz.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Abstract

omit [IsProbabilityMeasure P] in
theorem _root_.MeasureTheory.Integrable.fsub {f g : Ω → ℝ} (hf : Integrable f P)
    (hg : Integrable g P) : Integrable (fun ω => f ω - g ω) P :=
  hf.sub hg

lemma memLp_sq_two_of_four {f : Ω → ℝ} (hf : MemLp f 4 P) : MemLp (fun ω => f ω ^ 2) 2 P :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.pow 2)).2
    ((integrable_pow_of_memLp_four hf (k := 4) le_rfl).congr (ae_of_all _ fun ω => by simp only [Pi.pow_apply]; ring))

lemma memLp_mul_two_of_four {f g : Ω → ℝ} (hf : MemLp f 4 P) (hg : MemLp g 4 P) :
    MemLp (fun ω => f ω * g ω) 2 P :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)).2
    ((integrable_pow_mul_pow_of_memLp_four hf hg (p := 2) (q := 2) rfl).congr
      (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring))

omit [IsProbabilityMeasure P] in
lemma memLp_bdd_mul {a X : Ω → ℝ} (ham : AEStronglyMeasurable a P) (ha0 : ∀ ω, 0 ≤ a ω)
    (ha1 : ∀ ω, a ω ≤ 1) (hX : MemLp X 2 P) : MemLp (fun ω => a ω * X ω) 2 P :=
  hX.of_le (ham.mul hX.aestronglyMeasurable) (ae_of_all _ fun ω => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (ha0 ω)]; exact ha1 ω))

omit [IsProbabilityMeasure P] in
lemma memLp_bdd_mul_ae {a X : Ω → ℝ} (ham : AEStronglyMeasurable a P)
    (ha0 : ∀ᵐ ω ∂P, 0 ≤ a ω) (ha1 : ∀ᵐ ω ∂P, a ω ≤ 1) (hX : MemLp X 2 P) :
    MemLp (fun ω => a ω * X ω) 2 P :=
  hX.of_le (ham.mul hX.aestronglyMeasurable) (by
    filter_upwards [ha0, ha1] with ω h0 h1
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1))

lemma sqrt_le_mul_pow' {x α s : ℝ} {k : ℕ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (h : x ≤ α * s ^ (2 * k)) : Real.sqrt x ≤ Real.sqrt α * s ^ k := by
  calc Real.sqrt x ≤ Real.sqrt (α * (s ^ k) ^ 2) :=
        Real.sqrt_le_sqrt (h.trans_eq (by ring))
    _ = Real.sqrt α * s ^ k := by rw [Real.sqrt_mul hα, Real.sqrt_sq (by positivity)]

omit [IsProbabilityMeasure P] in
lemma abs_integral_mul_le_pow {X Y : Ω → ℝ} {α β s : ℝ} {i j : ℕ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hx : ∫ ω, X ω ^ 2 ∂P ≤ α * s ^ (2 * i)) (hy : ∫ ω, Y ω ^ 2 ∂P ≤ β * s ^ (2 * j)) :
    |∫ ω, X ω * Y ω ∂P| ≤ Real.sqrt α * Real.sqrt β * s ^ (i + j) := by
  refine (abs_integral_mul_le_sqrt hX hY).trans ?_
  calc Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, Y ω ^ 2 ∂P)
      ≤ (Real.sqrt α * s ^ i) * (Real.sqrt β * s ^ j) :=
        mul_le_mul (sqrt_le_mul_pow' hα hs hx) (sqrt_le_mul_pow' hβ hs hy)
          (Real.sqrt_nonneg _) (by positivity)
    _ = Real.sqrt α * Real.sqrt β * s ^ (i + j) := by rw [pow_add]; ring

lemma integral_sq_le_of_pow_four {X : Ω → ℝ} (hX : MemLp X 4 P) {c s : ℝ} {k : ℕ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (h : ∫ ω, X ω ^ 4 ∂P ≤ c * s ^ (2 * (2 * k))) :
    ∫ ω, X ω ^ 2 ∂P ≤ Real.sqrt c * s ^ (2 * k) := by
  have j := sq_integral_sq_le_integral_pow_four hX
  have h1 : ∫ ω, X ω ^ 2 ∂P ≤ Real.sqrt (∫ ω, X ω ^ 4 ∂P) :=
    (le_abs_self _).trans (Real.abs_le_sqrt j)
  exact h1.trans (sqrt_le_mul_pow' hc hs h)

lemma exp_neg_le_quad {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp (-x) := Real.exp_pos _
  have key : 0 ≤ (1 - x + x ^ 2 - Real.exp (-x)) * (1 + x) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hp.le, pow_nonneg hx 3]
  by_contra hc
  push Not at hc
  nlinarith

/-- **One step of the weighted energy estimate** (abstract form). -/
theorem weighted_step_le {a Iu Iv G W Q s2 : Ω → ℝ} {s M cR cI cQ cE cW : ℝ}
    (hs : 0 ≤ s) (hM : 0 ≤ M) (hcR : 0 ≤ cR) (hcI : 0 ≤ cI) (hcQ : 0 ≤ cQ) (hcE : 0 ≤ cE)
    (hcW : 0 ≤ cW)
    (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1) (ham : AEStronglyMeasurable a P)
    (hIu : MemLp Iu 4 P) (hIv : MemLp Iv 4 P) (hG : MemLp G 4 P) (hW : MemLp W 4 P)
    (hGW : MemLp (fun ω => G ω * W ω) 4 P) (hQ : MemLp Q 4 P) (hs2 : MemLp s2 2 P)
    (hQ0 : ∀ ω, 0 ≤ Q ω)
    (horth : ∫ ω, a ω * Iu ω * (Iv ω - Iu ω) ∂P = 0)
    (hind : ∫ ω, a ω * G ω ^ 2 * W ω ^ 2 ∂P = s ^ 2 * ∫ ω, a ω * G ω ^ 2 ∂P)
    (hGs : ∀ᵐ ω ∂P, G ω ^ 2 = Iu ω ^ 2 * s2 ω)
    (hR : ∫ ω, (Iv ω - Iu ω - G ω * W ω) ^ 4 ∂P ≤ cR * s ^ 8)
    (hdI : ∫ ω, (Iv ω - Iu ω) ^ 4 ∂P ≤ cI * s ^ 4)
    (hIu4 : ∫ ω, Iu ω ^ 4 ∂P ≤ M) (hIv4 : ∫ ω, Iv ω ^ 4 ∂P ≤ M) (hG4 : ∫ ω, G ω ^ 4 ∂P ≤ M)
    (hW4 : ∫ ω, W ω ^ 4 ∂P ≤ cW * s ^ 4) (hQ4 : ∫ ω, Q ω ^ 4 ∂P ≤ cQ * s ^ 8)
    (hE : ∫ ω, (Q ω - s ^ 2 * s2 ω) ^ 2 ∂P ≤ cE * s ^ 6) :
    ∫ ω, Iv ω ^ 2 * (a ω * Real.exp (-Q ω)) ∂P - ∫ ω, Iu ω ^ 2 * a ω ∂P ≤
      (2 * (Real.sqrt (Real.sqrt M * Real.sqrt cW) * Real.sqrt (Real.sqrt cR)) +
          Real.sqrt (Real.sqrt cI) * Real.sqrt (4 * Real.sqrt M * Real.sqrt cQ) +
          Real.sqrt M * Real.sqrt cE) * s ^ 3 +
        (Real.sqrt cR + Real.sqrt M * Real.sqrt cQ) * s ^ 4 := by
  -- basic memberships
  have two4 : (2 : ENNReal) ≤ 4 := by norm_num
  set R : Ω → ℝ := fun ω => Iv ω - Iu ω - G ω * W ω with hRdef
  have hRL : MemLp R 4 P := (hIv.sub hIu).sub hGW
  have hD : MemLp (fun ω => Iv ω - Iu ω) 4 P := hIv.sub hIu
  have hS : MemLp (fun ω => Iv ω + Iu ω) 4 P := hIv.add hIu
  have hQs : MemLp (fun ω => Q ω - s ^ 2 * s2 ω) 2 P :=
    (hQ.mono_exponent two4).sub (hs2.const_mul _)
  have mA : ∀ {X : Ω → ℝ}, MemLp X 2 P → MemLp (fun ω => a ω * X ω) 2 P :=
    fun hX => memLp_bdd_mul ham ha0 ha1 hX
  have ha2 : ∀ ω, a ω ^ 2 ≤ 1 := fun ω => by nlinarith [ha0 ω, ha1 ω]
  -- integrability of the eight terms
  have i1 : Integrable (fun ω => a ω * Iu ω * (Iv ω - Iu ω)) P :=
    integrable_mul_of_memLp_two (mA (hIu.mono_exponent two4)) (hD.mono_exponent two4)
  have i2 : Integrable (fun ω => a ω * G ω ^ 2 * W ω ^ 2) P :=
    integrable_mul_of_memLp_two (mA (memLp_sq_two_of_four hG)) (memLp_sq_two_of_four hW)
  have mGW2 : MemLp (fun ω => a ω * (G ω * W ω)) 2 P := mA (memLp_mul_two_of_four hG hW)
  have i3 : Integrable (fun ω => a ω * G ω * W ω * R ω) P :=
    (integrable_mul_of_memLp_two mGW2 (hRL.mono_exponent two4)).congr
      (ae_of_all _ fun ω => by ring)
  have i4 : Integrable (fun ω => a ω * R ω ^ 2) P :=
    (integrable_mul_of_memLp_two (mA (hRL.mono_exponent two4)) (hRL.mono_exponent two4)).congr
      (ae_of_all _ fun ω => by ring)
  have mIu2 : MemLp (fun ω => a ω * Iu ω ^ 2) 2 P := mA (memLp_sq_two_of_four hIu)
  have i5 : Integrable (fun ω => a ω * Iu ω ^ 2 * s2 ω) P :=
    integrable_mul_of_memLp_two mIu2 hs2
  have i6 : Integrable (fun ω => a ω * Iu ω ^ 2 * (Q ω - s ^ 2 * s2 ω)) P :=
    integrable_mul_of_memLp_two mIu2 hQs
  have mSQ : MemLp (fun ω => a ω * ((Iv ω + Iu ω) * Q ω)) 2 P := mA (memLp_mul_two_of_four hS hQ)
  have i7 : Integrable (fun ω => (Iv ω - Iu ω) * (a ω * ((Iv ω + Iu ω) * Q ω))) P :=
    integrable_mul_of_memLp_two (hD.mono_exponent two4) mSQ
  have mIv2 : MemLp (fun ω => a ω * Iv ω ^ 2) 2 P := mA (memLp_sq_two_of_four hIv)
  have i8 : Integrable (fun ω => a ω * Iv ω ^ 2 * Q ω ^ 2) P :=
    integrable_mul_of_memLp_two mIv2 (memLp_sq_two_of_four hQ)
  have hbm : AEStronglyMeasurable (fun ω => a ω * Real.exp (-Q ω)) P :=
    ham.mul (Real.continuous_exp.comp_aestronglyMeasurable hQ.aestronglyMeasurable.neg)
  have hb2 : MemLp (fun ω => a ω * Real.exp (-Q ω)) 2 P :=
    MemLp.of_bound hbm 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 ω) (Real.exp_pos _).le)]
      have : Real.exp (-Q ω) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith [hQ0 ω]
      nlinarith [ha0 ω, ha1 ω, Real.exp_pos (-Q ω)])
  have iL : Integrable (fun ω => Iv ω ^ 2 * (a ω * Real.exp (-Q ω))) P :=
    integrable_mul_of_memLp_two (memLp_sq_two_of_four hIv) hb2
  have iR : Integrable (fun ω => Iu ω ^ 2 * a ω) P :=
    integrable_mul_of_memLp_two (memLp_sq_two_of_four hIu)
      (MemLp.of_bound ham 1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ha0 ω)]; exact ha1 ω))
  -- pointwise inequality
  have iF := (((((((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)).fun_add i4).fsub
    (i5.const_mul (s ^ 2))).fsub i6).fsub i7).fun_add i8
  have hpt : ∀ ω, Iv ω ^ 2 * (a ω * Real.exp (-Q ω)) - Iu ω ^ 2 * a ω ≤
      2 * (a ω * Iu ω * (Iv ω - Iu ω)) + a ω * G ω ^ 2 * W ω ^ 2 +
        2 * (a ω * G ω * W ω * R ω) + a ω * R ω ^ 2 - s ^ 2 * (a ω * Iu ω ^ 2 * s2 ω) -
        a ω * Iu ω ^ 2 * (Q ω - s ^ 2 * s2 ω) -
        (Iv ω - Iu ω) * (a ω * ((Iv ω + Iu ω) * Q ω)) + a ω * Iv ω ^ 2 * Q ω ^ 2 := by
    intro ω
    have he := exp_neg_le_quad (hQ0 ω)
    have h1 := mul_le_mul_of_nonneg_left he (mul_nonneg (ha0 ω) (sq_nonneg (Iv ω)))
    have hid : 2 * (a ω * Iu ω * (Iv ω - Iu ω)) + a ω * G ω ^ 2 * W ω ^ 2 +
        2 * (a ω * G ω * W ω * R ω) + a ω * R ω ^ 2 - s ^ 2 * (a ω * Iu ω ^ 2 * s2 ω) -
        a ω * Iu ω ^ 2 * (Q ω - s ^ 2 * s2 ω) -
        (Iv ω - Iu ω) * (a ω * ((Iv ω + Iu ω) * Q ω)) + a ω * Iv ω ^ 2 * Q ω ^ 2 =
        a ω * Iv ω ^ 2 * (1 - Q ω + Q ω ^ 2) - Iu ω ^ 2 * a ω := by
      simp only [hRdef]; ring
    rw [hid]
    linarith
  have hmono := integral_mono (iL.fsub iR) iF hpt
  rw [integral_sub iL iR] at hmono
  rw [integral_add (((((((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)).fun_add i4).fsub
      (i5.const_mul (s ^ 2))).fsub i6).fsub i7) i8,
    integral_sub ((((((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)).fun_add i4).fsub
      (i5.const_mul (s ^ 2))).fsub i6) i7,
    integral_sub (((((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)).fun_add i4).fsub
      (i5.const_mul (s ^ 2))) i6,
    integral_sub ((((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)).fun_add i4) (i5.const_mul (s ^ 2)),
    integral_add (((i1.const_mul 2).fun_add i2).fun_add (i3.const_mul 2)) i4,
    integral_add ((i1.const_mul 2).fun_add i2) (i3.const_mul 2),
    integral_add (i1.const_mul 2) i2, integral_const_mul, integral_const_mul,
    integral_const_mul, horth] at hmono
  -- cancellation
  have hcan : ∫ ω, a ω * G ω ^ 2 * W ω ^ 2 ∂P = s ^ 2 * ∫ ω, a ω * Iu ω ^ 2 * s2 ω ∂P := by
    rw [hind]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hGs] with ω hω
    rw [hω]; ring
  -- bounds
  have hW2 : Real.sqrt (∫ ω, W ω ^ 4 ∂P) ≤ Real.sqrt cW * s ^ 2 :=
    sqrt_le_mul_pow' (k := 2) hcW hs (hW4.trans_eq (by ring))
  have hQ2 : Real.sqrt (∫ ω, Q ω ^ 4 ∂P) ≤ Real.sqrt cQ * s ^ 4 :=
    sqrt_le_mul_pow' (k := 4) hcQ hs (hQ4.trans_eq (by ring))
  have hM2 : ∀ {x : ℝ}, x ≤ M → Real.sqrt x ≤ Real.sqrt M := fun h => Real.sqrt_le_sqrt h
  have hR2 : ∫ ω, R ω ^ 2 ∂P ≤ Real.sqrt cR * s ^ (2 * 2) :=
    integral_sq_le_of_pow_four hRL hcR hs (hR.trans_eq (by ring))
  -- term 3
  have hX3 : ∫ ω, (a ω * (G ω * W ω)) ^ 2 ∂P ≤ (Real.sqrt M * Real.sqrt cW) * s ^ (2 * 1) := by
    have hi : Integrable (fun ω => G ω ^ 2 * W ω ^ 2) P :=
      integrable_pow_mul_pow_of_memLp_four hG hW (p := 2) (q := 2) rfl
    calc ∫ ω, (a ω * (G ω * W ω)) ^ 2 ∂P ≤ ∫ ω, G ω ^ 2 * W ω ^ 2 ∂P := by
          refine integral_mono mGW2.integrable_sq hi fun ω => ?_
          have : (a ω * (G ω * W ω)) ^ 2 = a ω ^ 2 * (G ω ^ 2 * W ω ^ 2) := by ring
          rw [this]
          exact mul_le_of_le_one_left (by positivity) (ha2 ω)
      _ ≤ Real.sqrt (∫ ω, G ω ^ 4 ∂P) * Real.sqrt (∫ ω, W ω ^ 4 ∂P) :=
          integral_sq_mul_sq_le hG hW
      _ ≤ Real.sqrt M * (Real.sqrt cW * s ^ 2) :=
          mul_le_mul (hM2 hG4) hW2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have B3 := abs_integral_mul_le_pow mGW2 (hRL.mono_exponent two4)
    (by positivity) (Real.sqrt_nonneg cR) hs hX3 hR2
  have e3 : ∫ ω, a ω * G ω * W ω * R ω ∂P = ∫ ω, a ω * (G ω * W ω) * R ω ∂P := by
    congr 1; funext ω; ring
  -- term 4
  have B4 : ∫ ω, a ω * R ω ^ 2 ∂P ≤ Real.sqrt cR * s ^ 4 := by
    have hi : Integrable (fun ω => R ω ^ 2) P := (hRL.mono_exponent two4).integrable_sq
    refine (integral_mono i4 hi fun ω => mul_le_of_le_one_left (sq_nonneg _) (ha1 ω)).trans ?_
    exact hR2.trans_eq (by ring)
  -- term 6
  have hX6 : ∫ ω, (a ω * Iu ω ^ 2) ^ 2 ∂P ≤ M * s ^ (2 * 0) := by
    have hi := integrable_pow_of_memLp_four hIu (k := 4) le_rfl
    calc ∫ ω, (a ω * Iu ω ^ 2) ^ 2 ∂P ≤ ∫ ω, Iu ω ^ 4 ∂P := by
          refine integral_mono mIu2.integrable_sq hi fun ω => ?_
          have : (a ω * Iu ω ^ 2) ^ 2 = a ω ^ 2 * Iu ω ^ 4 := by ring
          rw [this]
          exact mul_le_of_le_one_left (by positivity) (ha2 ω)
      _ ≤ M * s ^ (2 * 0) := by simpa using hIu4
  have B6 := abs_integral_mul_le_pow (j := 3) mIu2 hQs hM hcE hs hX6 (hE.trans_eq (by ring))
  -- term 7
  have hX7 : ∫ ω, (Iv ω - Iu ω) ^ 2 ∂P ≤ Real.sqrt cI * s ^ (2 * 1) :=
    integral_sq_le_of_pow_four hD hcI hs (hdI.trans_eq (by ring))
  have hY7 : ∫ ω, (a ω * ((Iv ω + Iu ω) * Q ω)) ^ 2 ∂P ≤
      (4 * Real.sqrt M * Real.sqrt cQ) * s ^ (2 * 2) := by
    have hi : Integrable (fun ω => (Iv ω + Iu ω) ^ 2 * Q ω ^ 2) P :=
      integrable_pow_mul_pow_of_memLp_four hS hQ (p := 2) (q := 2) rfl
    have hS4 : ∫ ω, (Iv ω + Iu ω) ^ 4 ∂P ≤ 16 * M := by
      have j1 := integrable_pow_of_memLp_four hIv (k := 4) le_rfl
      have j2 := integrable_pow_of_memLp_four hIu (k := 4) le_rfl
      calc ∫ ω, (Iv ω + Iu ω) ^ 4 ∂P ≤ ∫ ω, (8 * Iv ω ^ 4 + 8 * Iu ω ^ 4) ∂P :=
            integral_mono (integrable_pow_of_memLp_four hS (k := 4) le_rfl)
              ((j1.const_mul 8).add (j2.const_mul 8)) fun ω => add_pow_four_le_frozen _ _
        _ = 8 * ∫ ω, Iv ω ^ 4 ∂P + 8 * ∫ ω, Iu ω ^ 4 ∂P := by
            rw [integral_add (j1.const_mul 8) (j2.const_mul 8), integral_const_mul,
              integral_const_mul]
        _ ≤ 16 * M := by linarith
    have h16 : Real.sqrt (16 * M) = 4 * Real.sqrt M := by
      rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    calc ∫ ω, (a ω * ((Iv ω + Iu ω) * Q ω)) ^ 2 ∂P ≤ ∫ ω, (Iv ω + Iu ω) ^ 2 * Q ω ^ 2 ∂P := by
          refine integral_mono mSQ.integrable_sq hi fun ω => ?_
          have : (a ω * ((Iv ω + Iu ω) * Q ω)) ^ 2 =
              a ω ^ 2 * ((Iv ω + Iu ω) ^ 2 * Q ω ^ 2) := by ring
          rw [this]
          exact mul_le_of_le_one_left (by positivity) (ha2 ω)
      _ ≤ Real.sqrt (∫ ω, (Iv ω + Iu ω) ^ 4 ∂P) * Real.sqrt (∫ ω, Q ω ^ 4 ∂P) :=
          integral_sq_mul_sq_le hS hQ
      _ ≤ (4 * Real.sqrt M) * (Real.sqrt cQ * s ^ 4) :=
          mul_le_mul (h16 ▸ Real.sqrt_le_sqrt hS4) hQ2 (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have B7 := abs_integral_mul_le_pow (hD.mono_exponent two4) mSQ (Real.sqrt_nonneg cI)
    (by positivity) hs hX7 hY7
  -- term 8
  have B8 : ∫ ω, a ω * Iv ω ^ 2 * Q ω ^ 2 ∂P ≤ Real.sqrt M * Real.sqrt cQ * s ^ 4 := by
    have hi : Integrable (fun ω => Iv ω ^ 2 * Q ω ^ 2) P :=
      integrable_pow_mul_pow_of_memLp_four hIv hQ (p := 2) (q := 2) rfl
    calc ∫ ω, a ω * Iv ω ^ 2 * Q ω ^ 2 ∂P ≤ ∫ ω, Iv ω ^ 2 * Q ω ^ 2 ∂P := by
          refine integral_mono i8 hi fun ω => ?_
          have : a ω * Iv ω ^ 2 * Q ω ^ 2 = a ω * (Iv ω ^ 2 * Q ω ^ 2) := by ring
          rw [this]
          exact mul_le_of_le_one_left (by positivity) (ha1 ω)
      _ ≤ Real.sqrt (∫ ω, Iv ω ^ 4 ∂P) * Real.sqrt (∫ ω, Q ω ^ 4 ∂P) :=
          integral_sq_mul_sq_le hIv hQ
      _ ≤ Real.sqrt M * (Real.sqrt cQ * s ^ 4) :=
          mul_le_mul (hM2 hIv4) hQ2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  rw [e3] at hmono
  have a3 := le_abs_self (∫ ω, a ω * (G ω * W ω) * R ω ∂P)
  have a6 := neg_abs_le (∫ ω, a ω * Iu ω ^ 2 * (Q ω - s ^ 2 * s2 ω) ∂P)
  have a7 := neg_abs_le (∫ ω, (Iv ω - Iu ω) * (a ω * ((Iv ω + Iu ω) * Q ω)) ∂P)
  have p3 : s ^ (1 + 2) = s ^ 3 := by norm_num
  have p6 : s ^ (0 + 3) = s ^ 3 := by norm_num
  rw [p3] at B3 B7
  rw [p6] at B6
  linarith [hcan, B3, B4, B6, B7, B8, a3, a6, a7]

end Abstract

/-- `weighted_step_le` with the bounds `0 ≤ a ≤ 1`, `0 ≤ Q` required only almost surely. -/
theorem weighted_step_le_ae {a Iu Iv G W Q s2 : Ω → ℝ} {s M cR cI cQ cE cW : ℝ}
    (hs : 0 ≤ s) (hM : 0 ≤ M) (hcR : 0 ≤ cR) (hcI : 0 ≤ cI) (hcQ : 0 ≤ cQ) (hcE : 0 ≤ cE)
    (hcW : 0 ≤ cW)
    (ha0 : ∀ᵐ ω ∂P, 0 ≤ a ω) (ha1 : ∀ᵐ ω ∂P, a ω ≤ 1) (ham : AEStronglyMeasurable a P)
    (hIu : MemLp Iu 4 P) (hIv : MemLp Iv 4 P) (hG : MemLp G 4 P) (hW : MemLp W 4 P)
    (hGW : MemLp (fun ω => G ω * W ω) 4 P) (hQ : MemLp Q 4 P) (hs2 : MemLp s2 2 P)
    (hQ0 : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (horth : ∫ ω, a ω * Iu ω * (Iv ω - Iu ω) ∂P = 0)
    (hind : ∫ ω, a ω * G ω ^ 2 * W ω ^ 2 ∂P = s ^ 2 * ∫ ω, a ω * G ω ^ 2 ∂P)
    (hGs : ∀ᵐ ω ∂P, G ω ^ 2 = Iu ω ^ 2 * s2 ω)
    (hR : ∫ ω, (Iv ω - Iu ω - G ω * W ω) ^ 4 ∂P ≤ cR * s ^ 8)
    (hdI : ∫ ω, (Iv ω - Iu ω) ^ 4 ∂P ≤ cI * s ^ 4)
    (hIu4 : ∫ ω, Iu ω ^ 4 ∂P ≤ M) (hIv4 : ∫ ω, Iv ω ^ 4 ∂P ≤ M) (hG4 : ∫ ω, G ω ^ 4 ∂P ≤ M)
    (hW4 : ∫ ω, W ω ^ 4 ∂P ≤ cW * s ^ 4) (hQ4 : ∫ ω, Q ω ^ 4 ∂P ≤ cQ * s ^ 8)
    (hE : ∫ ω, (Q ω - s ^ 2 * s2 ω) ^ 2 ∂P ≤ cE * s ^ 6) :
    ∫ ω, Iv ω ^ 2 * (a ω * Real.exp (-Q ω)) ∂P - ∫ ω, Iu ω ^ 2 * a ω ∂P ≤
      (2 * (Real.sqrt (Real.sqrt M * Real.sqrt cW) * Real.sqrt (Real.sqrt cR)) +
          Real.sqrt (Real.sqrt cI) * Real.sqrt (4 * Real.sqrt M * Real.sqrt cQ) +
          Real.sqrt M * Real.sqrt cE) * s ^ 3 +
        (Real.sqrt cR + Real.sqrt M * Real.sqrt cQ) * s ^ 4 := by
  set a' : Ω → ℝ := fun ω => max 0 (min (a ω) 1) with ha'
  set Q' : Ω → ℝ := fun ω => max 0 (Q ω) with hQ'
  have hea : a =ᵐ[P] a' := by
    filter_upwards [ha0, ha1] with ω h0 h1
    simp only [ha', min_eq_left h1, max_eq_right h0]
  have heQ : Q =ᵐ[P] Q' := by
    filter_upwards [hQ0] with ω h0
    simp only [hQ', max_eq_right h0]
  have h1 := weighted_step_le (P := P) (a := a') (Q := Q') hs hM hcR hcI hcQ hcE hcW
    (fun ω => le_max_left _ _) (fun ω => max_le zero_le_one (min_le_right _ _))
    (ham.congr hea) hIu hIv hG hW hGW (hQ.ae_eq heQ) hs2 (fun ω => le_max_left _ _)
    (by rw [← horth]; exact integral_congr_ae (by filter_upwards [hea] with ω h; rw [h]))
    (by
      rw [integral_congr_ae (show (fun ω => a' ω * G ω ^ 2 * W ω ^ 2) =ᵐ[P]
          fun ω => a ω * G ω ^ 2 * W ω ^ 2 by filter_upwards [hea] with ω h; rw [h]),
        integral_congr_ae (show (fun ω => a' ω * G ω ^ 2) =ᵐ[P] fun ω => a ω * G ω ^ 2 by
          filter_upwards [hea] with ω h; rw [h])]
      exact hind)
    hGs hR hdI hIu4 hIv4 hG4 hW4
    (by rw [← integral_congr_ae (show (fun ω => Q ω ^ 4) =ᵐ[P] fun ω => Q' ω ^ 4 by
          filter_upwards [heQ] with ω h; rw [h])]; exact hQ4)
    (by rw [← integral_congr_ae (show (fun ω => (Q ω - s ^ 2 * s2 ω) ^ 2) =ᵐ[P]
          fun ω => (Q' ω - s ^ 2 * s2 ω) ^ 2 by filter_upwards [heQ] with ω h; rw [h])]
        exact hE)
  rw [integral_congr_ae (show (fun ω => Iv ω ^ 2 * (a ω * Real.exp (-Q ω))) =ᵐ[P]
      fun ω => Iv ω ^ 2 * (a' ω * Real.exp (-Q' ω)) by
        filter_upwards [hea, heQ] with ω h h'; rw [h, h']),
    integral_congr_ae (show (fun ω => Iu ω ^ 2 * a ω) =ᵐ[P] fun ω => Iu ω ^ 2 * a' ω by
      filter_upwards [hea] with ω h; rw [h])]
  exact h1

end SignatureVolatility
