module

public import Mathlib.Probability.Independence.Integration


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SignatureVolatility

/-!
# Fourth moments of independent sums and almost-sure convergence

Elementary probability used to upgrade `L²` quadratic-variation statements to **almost-sure,
full-sequence** convergence along the (non-nested) uniform grids of the `limUnder` Itô kit:

* `integral_sum_pow_four_le`: for independent, centred, `L⁴` variables with fourth moments
  bounded by `M`, `𝔼[(∑_{i ∈ s} X_i)⁴] ≤ 9 |s|² M`;
* `ae_tendsto_zero_of_summable_integral_pow_four`: summable fourth moments force almost-sure
  convergence to `0` (Borel–Cantelli in the form `∑ₙ Aₙ⁴ < ∞` a.s.).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Powers up to the fourth of an `L⁴` variable are integrable. -/
lemma integrable_pow_of_memLp_four {f : Ω → ℝ} (hf : MemLp f 4 P) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => f ω ^ k) P := by
  have h1 : MemLp f (k : ℝ≥0∞) P := hf.mono_exponent (by exact_mod_cast hk)
  have h2 : Integrable (fun ω => ‖f ω‖ ^ k) P := h1.integrable_norm_pow'
  refine (integrable_norm_iff (hf.aestronglyMeasurable.pow k)).mp ?_
  simpa [norm_pow] using h2

/-- Jensen for the square: `(𝔼 f²)² ≤ 𝔼 f⁴` on a probability space. -/
lemma sq_integral_sq_le_integral_pow_four {f : Ω → ℝ} (hf : MemLp f 4 P) :
    (∫ ω, f ω ^ 2 ∂P) ^ 2 ≤ ∫ ω, f ω ^ 4 ∂P := by
  set m := ∫ ω, f ω ^ 2 ∂P with hm
  have h2 := integrable_pow_of_memLp_four hf (k := 2) (by norm_num)
  have h4 := integrable_pow_of_memLp_four hf (k := 4) le_rfl
  have hnn : 0 ≤ ∫ ω, (f ω ^ 2 - m) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have heq : ∫ ω, (f ω ^ 2 - m) ^ 2 ∂P = ∫ ω, f ω ^ 4 ∂P - m ^ 2 := by
    have h : (fun ω => (f ω ^ 2 - m) ^ 2) = fun ω => f ω ^ 4 + -(2 * m) * f ω ^ 2 + m ^ 2 := by
      funext ω; ring
    rw [h, integral_add (h4.fun_add (h2.const_mul _)) (integrable_const _),
      integral_add h4 (h2.const_mul _), integral_const_mul, integral_const, ← hm]
    simp
    ring
  linarith

/-- **Fourth moment of an independent centred sum.** -/
theorem integral_sum_pow_four_le {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X P)
    (hmeas : ∀ i, Measurable (X i)) (hLp : ∀ i, MemLp (X i) 4 P)
    (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) {M : ℝ} (hM : ∀ i, ∫ ω, X i ω ^ 4 ∂P ≤ M) (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂P ≤ 9 * (s.card : ℝ) ^ 2 * M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hM0 : 0 ≤ M := (integral_nonneg fun ω => by positivity).trans (hM a)
    set S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω with hS
    set Y : Ω → ℝ := X a with hY
    have hSLp : MemLp S 4 P := by
      have h := memLp_finsetSum' (p := 4) (μ := P) s fun i _ => hLp i
      have hfun : (∑ j ∈ s, X j) = S := by funext ω; simp [S]
      rwa [hfun] at h
    have hSm : Measurable S := Finset.measurable_sum _ fun i _ => hmeas i
    have hindep : IndepFun S Y P := by
      have h := hind.indepFun_finsetSum_of_notMem hmeas ha
      have hfun : (∑ j ∈ s, X j) = S := by funext ω; simp [S]
      rwa [hfun] at h
    have key : ∀ p q : ℕ, ∫ ω, S ω ^ p * Y ω ^ q ∂P =
        (∫ ω, S ω ^ p ∂P) * ∫ ω, Y ω ^ q ∂P := fun p q =>
      hindep.integral_fun_comp_mul_comp (f := fun x : ℝ => x ^ p) (g := fun y : ℝ => y ^ q)
        hSm.aemeasurable (hmeas a).aemeasurable
        (measurable_id.pow_const p).aestronglyMeasurable
        (measurable_id.pow_const q).aestronglyMeasurable
    have hint : ∀ p q : ℕ, p ≤ 4 → q ≤ 4 → Integrable (fun ω => S ω ^ p * Y ω ^ q) P :=
      fun p q hp hq =>
        (hindep.comp (measurable_id.pow_const p) (measurable_id.pow_const q)).integrable_mul
          (integrable_pow_of_memLp_four hSLp hp) (integrable_pow_of_memLp_four (hLp a) hq)
    have I40 := hint 4 0 (by norm_num) (by norm_num)
    have I31 := (hint 3 1 (by norm_num) (by norm_num)).const_mul 4
    have I22 := (hint 2 2 (by norm_num) (by norm_num)).const_mul 6
    have I13 := (hint 1 3 (by norm_num) (by norm_num)).const_mul 4
    have I04 := hint 0 4 (by norm_num) (by norm_num)
    have hexp : (fun ω => (∑ i ∈ insert a s, X i ω) ^ 4) = fun ω =>
        S ω ^ 4 * Y ω ^ 0 + 4 * (S ω ^ 3 * Y ω ^ 1) + 6 * (S ω ^ 2 * Y ω ^ 2) +
          4 * (S ω ^ 1 * Y ω ^ 3) + S ω ^ 0 * Y ω ^ 4 := by
      funext ω
      rw [Finset.sum_insert ha]
      simp only [S, Y]
      ring
    have hS1 : ∫ ω, S ω ^ 1 ∂P = 0 := by
      simp only [pow_one, S]
      rw [integral_finsetSum _ fun i _ => (hLp i).integrable (by norm_num)]
      exact Finset.sum_eq_zero fun i _ => h0 i
    have hY1 : ∫ ω, Y ω ^ 1 ∂P = 0 := by simpa using h0 a
    have hS0 : ∫ ω, S ω ^ 0 ∂P = 1 := by simp
    have hY0 : ∫ ω, Y ω ^ 0 ∂P = 1 := by simp
    -- second-moment bounds
    have hu := sq_integral_sq_le_integral_pow_four hSLp
    have hv := sq_integral_sq_le_integral_pow_four (hLp a)
    have hu0 : 0 ≤ ∫ ω, S ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have hv0 : 0 ≤ ∫ ω, Y ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have hk0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    have huv : (∫ ω, S ω ^ 2 ∂P) * (∫ ω, Y ω ^ 2 ∂P) ≤ 3 * s.card * M := by
      have hsq : ((∫ ω, S ω ^ 2 ∂P) * (∫ ω, Y ω ^ 2 ∂P)) ^ 2 ≤ (3 * s.card * M) ^ 2 := by
        calc ((∫ ω, S ω ^ 2 ∂P) * (∫ ω, Y ω ^ 2 ∂P)) ^ 2
            = (∫ ω, S ω ^ 2 ∂P) ^ 2 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 := by ring
          _ ≤ (9 * (s.card : ℝ) ^ 2 * M) * M :=
              mul_le_mul (hu.trans ih) (hv.trans (hM a)) (sq_nonneg _) (by positivity)
          _ = (3 * s.card * M) ^ 2 := by ring
      exact (le_abs_self _).trans (abs_le_of_sq_le_sq hsq (by positivity))
    rw [hexp, integral_add ((((I40.fun_add I31).fun_add I22).fun_add I13)) I04,
      integral_add ((I40.fun_add I31).fun_add I22) I13, integral_add (I40.fun_add I31) I22,
      integral_add I40 I31, integral_const_mul, integral_const_mul, integral_const_mul,
      key 4 0, key 3 1, key 2 2, key 1 3, key 0 4, hS1, hY1, hS0, hY0,
      Finset.card_insert_of_notMem ha]
    have h4 := hM a
    push_cast
    nlinarith [mul_nonneg hk0 hM0]

omit [IsProbabilityMeasure P] in
/-- **Summable fourth moments ⇒ almost-sure convergence to zero.** -/
theorem ae_tendsto_zero_of_summable_integral_pow_four {A : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (A n)) (hint : ∀ n, Integrable (fun ω => A n ω ^ 4) P)
    {b : ℕ → ℝ} (hb : Summable b) (hle : ∀ n, ∫ ω, A n ω ^ 4 ∂P ≤ b n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 0) := by
  have hmeas4 : ∀ n, Measurable fun ω => ENNReal.ofReal (A n ω ^ 4) := fun n =>
    ((hmeas n).pow_const 4).ennreal_ofReal
  have h1 : ∫⁻ ω, ∑' n, ENNReal.ofReal (A n ω ^ 4) ∂P ≠ ∞ := by
    rw [lintegral_tsum fun n => (hmeas4 n).aemeasurable]
    have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal (A n ω ^ 4) ∂P ≤ ENNReal.ofReal (b n) := fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ fun ω => by positivity)]
      exact ENNReal.ofReal_le_ofReal (hle n)
    exact ne_top_of_le_ne_top hb.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hn)
  filter_upwards [ae_lt_top (Measurable.tsum hmeas4) h1] with ω hω
  have h3 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h4 : Tendsto (fun n => A n ω ^ 4) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
    simp only [Function.comp_def, ENNReal.toReal_zero] at h
    refine h.congr fun n => ENNReal.toReal_ofReal (by positivity)
  have h5 : Tendsto (fun n => Real.sqrt (Real.sqrt (A n ω ^ 4))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.comp Real.continuous_sqrt).tendsto 0
    simp only [Function.comp_def, Real.sqrt_zero] at h
    exact h.comp h4
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr (h5.congr fun n => ?_)
  rw [show A n ω ^ 4 = (A n ω ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

end SignatureVolatility
