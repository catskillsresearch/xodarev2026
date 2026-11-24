module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# C3c. Differentiating the Gaussian product exponential under the integral
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma integrable_exp_mul_abs_gaussianReal (c : ℝ) {μ : ℝ} {v : ℝ≥0} :
    Integrable (fun x : ℝ => Real.exp (c * |x|)) (gaussianReal μ v) := by
  refine ((integrable_exp_mul_gaussianReal (μ := μ) (v := v) c).add
      (integrable_exp_mul_gaussianReal (μ := μ) (v := v) (-c))).mono'
    (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Pi.add_apply]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- The `j`-th derivative at `0` of
`r ↦ ∫ exp(r (x + i √t y)) d(γ_t ⊗ γ_1)` is the corresponding moment. -/
lemma iteratedDeriv_integral_cexp_gaussianReal_prod (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv j (fun r : ℂ =>
      ∫ p : ℝ × ℝ,
        Complex.exp (r * ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)))
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1))) 0 =
      ∫ p : ℝ × ℝ,
        ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) ^ j
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)) := by
  set μ := (gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)
  set Z : ℝ × ℝ → ℂ :=
    fun p => (p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)
  have hnormZ : ∀ p, ‖Z p‖ ≤ |p.1| + Real.sqrt t * |p.2| := fun p => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
  have hInt_exp : ∀ R : ℝ, 0 ≤ R → Integrable (fun p : ℝ × ℝ => Real.exp (R * ‖Z p‖)) μ :=
    fun R hR => by
      have h1 : Integrable (fun x : ℝ => Real.exp (R * |x|))
          (gaussianReal 0 (Real.toNNReal t)) :=
        integrable_exp_mul_abs_gaussianReal R
      have h2 : Integrable (fun y : ℝ => Real.exp (R * Real.sqrt t * |y|))
          (gaussianReal 0 1) :=
        integrable_exp_mul_abs_gaussianReal (R * Real.sqrt t)
      refine (h1.mul_prod h2).mono' (by fun_prop : Continuous _).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      calc R * ‖Z p‖
          ≤ R * (|p.1| + Real.sqrt t * |p.2|) :=
            mul_le_mul_of_nonneg_left (hnormZ p) hR
        _ = R * |p.1| + (R * Real.sqrt t) * |p.2| := by ring
  have hpow_le : ∀ (n : ℕ) (p : ℝ × ℝ),
      ‖Z p‖ ^ n ≤ (n.factorial : ℝ) * Real.exp (‖Z p‖) := fun n p => by
    have hx := Real.pow_div_factorial_le_exp (x := ‖Z p‖) (norm_nonneg (Z p)) n
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
    rw [div_le_iff₀ hfac] at hx
    linarith
  have hInt : ∀ (k : ℕ) (ρ : ℂ),
      Integrable (fun p : ℝ × ℝ => Z p ^ k * Complex.exp (ρ * Z p)) μ := fun k ρ => by
    refine ((hInt_exp (‖ρ‖ + 1) (by positivity)).const_mul (k.factorial : ℝ)).mono'
      (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    calc ‖Z p ^ k * Complex.exp (ρ * Z p)‖
        = ‖Z p‖ ^ k * ‖Complex.exp (ρ * Z p)‖ := by rw [norm_mul, norm_pow]
      _ = ‖Z p‖ ^ k * Real.exp (ρ * Z p).re := by rw [Complex.norm_exp]
      _ ≤ ‖Z p‖ ^ k * Real.exp (‖ρ * Z p‖) := by
          gcongr; exact Complex.re_le_norm _
      _ = ‖Z p‖ ^ k * Real.exp (‖ρ‖ * ‖Z p‖) := by rw [norm_mul]
      _ ≤ (k.factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (‖ρ‖ * ‖Z p‖) := by
          gcongr; exact hpow_le k p
      _ = (k.factorial : ℝ) * Real.exp ((‖ρ‖ + 1) * ‖Z p‖) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hderiv : ∀ (k : ℕ) (r : ℂ),
      HasDerivAt (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) ∂μ)
        (∫ p : ℝ × ℝ, Z p ^ (k + 1) * Complex.exp (r * Z p) ∂μ) r := fun k r => by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (ρ : ℂ) (p : ℝ × ℝ) => Z p ^ k * Complex.exp (ρ * Z p))
      (F' := fun (ρ : ℂ) (p : ℝ × ℝ) => Z p ^ (k + 1) * Complex.exp (ρ * Z p))
      (bound := fun p => (k + 1).factorial * Real.exp ((‖r‖ + 2) * ‖Z p‖))
      (s := Metric.ball r 1) (x₀ := r) (Metric.ball_mem_nhds r one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun ρ => (by fun_prop : Continuous _).aestronglyMeasurable
    · exact hInt k r
    · exact (hInt (k + 1) r).aestronglyMeasurable
    · refine ae_of_all _ fun p ρ hρ => ?_
      have hρbd : ‖ρ‖ ≤ ‖r‖ + 1 := by
        have hdist : ‖ρ - r‖ < 1 := by
          simpa [dist_eq_norm] using (Metric.mem_ball.mp hρ)
        calc ‖ρ‖ = ‖(ρ - r) + r‖ := by simp
          _ ≤ ‖ρ - r‖ + ‖r‖ := norm_add_le _ _
          _ ≤ 1 + ‖r‖ := by linarith [le_of_lt hdist]
          _ = ‖r‖ + 1 := by ring
      calc ‖Z p ^ (k + 1) * Complex.exp (ρ * Z p)‖
          = ‖Z p‖ ^ (k + 1) * Real.exp (ρ * Z p).re := by
            rw [norm_mul, norm_pow, Complex.norm_exp]
        _ ≤ ‖Z p‖ ^ (k + 1) * Real.exp (‖ρ * Z p‖) := by
            gcongr; exact Complex.re_le_norm _
        _ = ‖Z p‖ ^ (k + 1) * Real.exp (‖ρ‖ * ‖Z p‖) := by
            rw [norm_mul]
        _ ≤ ((k + 1).factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp (‖ρ‖ * ‖Z p‖) :=
            mul_le_mul_of_nonneg_right (hpow_le (k + 1) p) (Real.exp_nonneg _)
        _ ≤ ((k + 1).factorial : ℝ) * Real.exp (‖Z p‖) * Real.exp ((‖r‖ + 1) * ‖Z p‖) := by
            gcongr
        _ = (k + 1).factorial * Real.exp ((‖r‖ + 2) * ‖Z p‖) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    · exact (hInt_exp (‖r‖ + 2) (by positivity)).const_mul _
    · refine ae_of_all _ fun p ρ _ => ?_
      have h1 : HasDerivAt (fun ρ : ℂ => ρ * Z p) (Z p) ρ := by
        simpa using (hasDerivAt_id ρ).mul_const (Z p)
      have h2 : HasDerivAt (fun ρ : ℂ => Complex.exp (ρ * Z p))
          (Complex.exp (ρ * Z p) * Z p) ρ := h1.cexp
      have hmul : HasDerivAt (fun ρ : ℂ => Z p ^ k * Complex.exp (ρ * Z p))
          (Z p ^ k * (Complex.exp (ρ * Z p) * Z p)) ρ :=
        h2.const_mul (Z p ^ k)
      convert hmul using 1
      ring
  have hgen : ∀ (k j : ℕ) (r : ℂ),
      iteratedDeriv j (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) ∂μ) r =
        ∫ p : ℝ × ℝ, Z p ^ (k + j) * Complex.exp (r * Z p) ∂μ := by
    intro k j
    induction j generalizing k with
    | zero =>
      intro r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      intro r
      rw [iteratedDeriv_succ']
      have hder : deriv (fun ρ : ℂ => ∫ p : ℝ × ℝ, Z p ^ k * Complex.exp (ρ * Z p) ∂μ) =
          fun ρ => ∫ p : ℝ × ℝ, Z p ^ (k + 1) * Complex.exp (ρ * Z p) ∂μ :=
        funext fun ρ => (hderiv k ρ).deriv
      rw [hder, ih (k + 1) r]
      simp [add_assoc, add_comm, add_left_comm]
  have h0 := hgen 0 j 0
  simp only [zero_add, pow_zero, one_mul, zero_mul, Complex.exp_zero] at h0
  simpa [μ, Z] using h0

end SignatureVolatility
