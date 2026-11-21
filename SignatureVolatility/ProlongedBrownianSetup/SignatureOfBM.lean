module

public import SignatureVolatility.ExtTensorAlgebra.TensorExpLevelNorm
public import SignatureVolatility.ExtTensorAlgebra.TensorExpNeg
public import SignatureVolatility.ExtTensorAlgebra.TensorExpShuffle
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- Coefficients of `exp⊗(v ω)` are measurable when the coordinates of `v` are. -/
lemma measurable_tensorExp_coeff {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {v : Ω → Fin d → ℝ} (hv : ∀ j, Measurable[m] (fun ω => v ω j)) (I : Word d) :
    Measurable[m] (fun ω => (tensorExp (v ω)).coeff I) := by
  have hprod : Measurable[m] (fun ω => (I.map (v ω)).prod) := by
    induction I with
    | nil => simp
    | cons i I ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (hv i).mul ih
  exact hprod.div_const _

/-- Coefficients of a concatenation are measurable when both factors' coefficients are. -/
lemma measurable_concat_coeff {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {a b : Ω → ExtTensorAlgebra d}
    (ha : ∀ I, Measurable[m] (fun ω => (a ω).coeff I))
    (hb : ∀ I, Measurable[m] (fun ω => (b ω).coeff I)) (I : Word d) :
    Measurable[m] (fun ω => (a ω ⊗ₜ b ω).coeff I) := by
  change Measurable[m] (fun ω =>
    ∑ k ∈ Finset.range (I.length + 1), (a ω).coeff (I.take k) * (b ω).coeff (I.drop k))
  exact Finset.measurable_sum _ fun k _ => (ha (I.take k)).mul (hb (I.drop k))

/-- Coefficients of `exp⊗(x − y) ⊗ exp⊗(z − x)` are measurable when the coordinates of
`x`, `y`, `z` are. -/
lemma measurable_tensorExp_sub_concat_coeff {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {x y z : Ω → Fin d → ℝ} (hx : ∀ j, Measurable[m] (fun ω => x ω j))
    (hy : ∀ j, Measurable[m] (fun ω => y ω j)) (hz : ∀ j, Measurable[m] (fun ω => z ω j))
    (I : Word d) :
    Measurable[m] (fun ω =>
      (tensorExp (fun j => x ω j - y ω j) ⊗ₜ tensorExp (fun j => z ω j - x ω j)).coeff I) :=
  measurable_concat_coeff
    (fun J => measurable_tensorExp_coeff (fun j => (hx j).sub (hy j)) J)
    (fun J => measurable_tensorExp_coeff (fun j => (hz j).sub (hx j)) J) I

/-- Level-1 coefficients of a concatenation. -/
lemma concat_coeff_singleton {d : ℕ} (a b : ExtTensorAlgebra d) (i : Fin d) :
    (a ⊗ₜ b).coeff [i] = a.coeff [] * b.coeff [i] + a.coeff [i] * b.coeff [] := by
  simp [concat, Finset.sum_range_succ]

end ExtTensorAlgebra

open ExtTensorAlgebra

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Running chordal signature from time `0`: `S_t = exp⊗(X_t − X_0)`. -/
def runningSig (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  tensorExp (fun j => MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j)

/-- Multiplicative chordal signature: `S_s⁻¹ ⊗ S_t`. -/
def sig2OfBrownian (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  tensorExp (fun j => MultiBrownian.wAug B 0 ω j - MultiBrownian.wAug B s ω j) ⊗ₜ
    runningSig B t ω

lemma sig2OfBrownian_meas (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (sig2OfBrownian B s t ω).coeff I) :=
  measurable_tensorExp_sub_concat_coeff (MultiBrownian.wAug_meas B 0)
    (MultiBrownian.wAug_meas B s) (MultiBrownian.wAug_meas B t) I

lemma sig2OfBrownian_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2OfBrownian B s t ω).coeff [] = 1 := by
  simp [sig2OfBrownian, runningSig, concat]

lemma sig2OfBrownian_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2OfBrownian B s t ω).coeff [0] = t - s := by
  simp only [sig2OfBrownian, runningSig, concat_coeff_singleton, tensorExp_coeff_nil,
    tensorExp_coeff_singleton]
  simp [MultiBrownian.wAug]
  ring

lemma sig2OfBrownian_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (sig2OfBrownian B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp only [sig2OfBrownian, runningSig, concat_coeff_singleton, tensorExp_coeff_nil,
    tensorExp_coeff_singleton]
  simp [MultiBrownian.wAug]

/-- From time `0` the two-parameter signature is the running signature. -/
lemma sig2OfBrownian_zero_left (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) :
    sig2OfBrownian B 0 t ω = runningSig B t ω := by
  simp only [sig2OfBrownian, sub_self]
  exact concat_tensorExp_zero_left _

/-- Chen's identity for the multiplicative chordal signature (valid for all `s`, `t`). -/
lemma sig2OfBrownian_chen (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    sig2OfBrownian B 0 t ω = sig2OfBrownian B 0 s ω ⊗ₜ sig2OfBrownian B s t ω := by
  have hneg : (fun j => MultiBrownian.wAug B 0 ω j - MultiBrownian.wAug B s ω j) =
      -(fun j => MultiBrownian.wAug B s ω j - MultiBrownian.wAug B 0 ω j) := by
    funext j
    simp
  rw [sig2OfBrownian_zero_left, sig2OfBrownian_zero_left]
  simp only [sig2OfBrownian]
  rw [← concat_assoc, hneg]
  simp only [runningSig]
  rw [tensorExp_neg]
  exact (concat_tensorExp_zero_left _).symm

/-- Shuffle (group-like) identity for the signature started at time `0`. -/
lemma sig2OfBrownian_shuffle (B : MultiBrownian Ω P d) (t : ℝ) (I J : Word (d + 1)) (ω : Ω) :
    (sig2OfBrownian B 0 t ω).coeff I * (sig2OfBrownian B 0 t ω).coeff J =
      evalShuffleBasis I J (sig2OfBrownian B 0 t ω) := by
  rw [sig2OfBrownian_zero_left]
  exact tensorExp_shuffle _ I J

/-- Exact level norms of the signature started at `0`: `‖X_t − X_0‖₂ⁿ / n!`. -/
lemma sig2OfBrownian_levelNorm (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) (n : ℕ) :
    (sig2OfBrownian B 0 t ω).levelNorm n =
      Real.sqrt (∑ j, (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j) ^ 2) ^ n /
        (n.factorial : ℝ) := by
  rw [sig2OfBrownian_zero_left]
  exact tensorExp_levelNorm _ n

/-- Adaptedness: `sig2 0 s` is measurable w.r.t. the path of `W` up to `t ≥ s`. -/
lemma sig2OfBrownian_adapted (B : MultiBrownian Ω P d) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t})
    (I : Word (d + 1)) :
    Measurable[(generatedFiltration (fun u i ω => MultiBrownian.W B u ω i)
      (MultiBrownian.W_meas B)).σAlg t] (fun ω => (sig2OfBrownian B 0 s.1 ω).coeff I) := by
  have hX : ∀ (u : {u : ℝ // 0 ≤ u ∧ u ≤ t}) (j : Fin (d + 1)),
      Measurable[(generatedFiltration (fun u i ω => MultiBrownian.W B u ω i)
        (MultiBrownian.W_meas B)).σAlg t] (fun ω => MultiBrownian.wAug B u.1 ω j) := by
    intro u j
    by_cases h : (j : ℕ) = 0
    · simp [MultiBrownian.wAug, h]
    · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
      exact (comap_measurable _).mono (le_iSup_of_le u (le_iSup_of_le _ le_rfl)) le_rfl
  have h0 := hX ⟨0, le_rfl, s.2.1.trans s.2.2⟩
  exact measurable_tensorExp_sub_concat_coeff h0 h0 (hX s) I

/-! ### Level-norm series of the chordal signature -/

/-- Euclidean norm `‖X_t − X_0‖₂` of the time-augmented increment. -/
def incrNorm (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt (∑ j, (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j) ^ 2)

lemma incrNorm_nonneg (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) : 0 ≤ incrNorm B t ω :=
  Real.sqrt_nonneg _

lemma sig2OfBrownian_levelNorm_eq (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) (n : ℕ) :
    (sig2OfBrownian B 0 t ω).levelNorm n = incrNorm B t ω ^ n / (n.factorial : ℝ) :=
  sig2OfBrownian_levelNorm B t ω n

lemma measurable_incrNorm (B : MultiBrownian Ω P d) (t : ℝ) :
    Measurable (incrNorm B t) :=
  (Finset.measurable_sum _ fun j _ =>
    ((MultiBrownian.wAug_meas B t j).sub (MultiBrownian.wAug_meas B 0 j)).pow_const 2).sqrt

lemma incrNorm_le_sum_abs (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) :
    incrNorm B t ω ≤ ∑ j, |MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j| := by
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j => |MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j|)
    (fun _ _ => abs_nonneg _)
  simpa only [sq_abs] using h

/-- Pathwise convergence of the weighted level series: this half of
`ProlongedBrownianSetup.factorial_moment_control` holds as stated. -/
lemma sig2OfBrownian_summable_levelNorm (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω)
    {w_fn : ℕ → ℝ}
    (hw : ∀ R : ℝ, 0 ≤ R → Summable (fun n : ℕ => w_fn n * (R ^ n / (n.factorial : ℝ)))) :
    Summable (fun n : ℕ => w_fn n * (sig2OfBrownian B 0 t ω).levelNorm n) := by
  simp only [sig2OfBrownian_levelNorm_eq]
  exact hw _ (incrNorm_nonneg B t ω)

/-- Every coordinate of the time-augmented increment has all exponential moments: the time
coordinate is deterministic and each Brownian coordinate is centred Gaussian. -/
lemma integrable_exp_mul_wAug_sub (B : MultiBrownian Ω P d) (t a : ℝ) (j : Fin (d + 1)) :
    Integrable
      (fun ω => Real.exp (a * (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j))) P := by
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
    exact integrable_const _
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte, MultiBrownian.W_zero, sub_zero]
    exact ((B.isBrownian _).toIsPreBrownianReal.hasLaw_eval (Real.toNNReal t)).integrable_comp
      (ProbabilityTheory.integrable_exp_mul_gaussianReal a)

/-- The increment norm has all exponential moments. Coordinates of `B` need not be
independent: the bound goes through the largest coordinate. -/
lemma integrable_exp_mul_incrNorm (B : MultiBrownian Ω P d) (t : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun ω => Real.exp (c * incrNorm B t ω)) P := by
  set K : ℝ := c * ((d : ℝ) + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  let v : Ω → Fin (d + 1) → ℝ :=
    fun ω j => MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j
  have hdom : Integrable
      (fun ω => ∑ j, (Real.exp (K * v ω j) + Real.exp (-K * v ω j))) P :=
    integrable_finsetSum _ fun j _ =>
      (integrable_exp_mul_wAug_sub B t K j).add (integrable_exp_mul_wAug_sub B t (-K) j)
  refine hdom.mono' ((measurable_incrNorm B t).const_mul c).exp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => |v ω j|)
    Finset.univ_nonempty
  have hsum : ∑ j, |v ω j| ≤ ((d : ℝ) + 1) * |v ω j₀| := by
    calc ∑ j, |v ω j| ≤ ∑ _j : Fin (d + 1), |v ω j₀| :=
          Finset.sum_le_sum fun j hj => hj₀ j hj
      _ = ((d : ℝ) + 1) * |v ω j₀| := by simp
  have hterm : Real.exp (K * |v ω j₀|) ≤
      Real.exp (K * v ω j₀) + Real.exp (-K * v ω j₀) := by
    rcases abs_choice (v ω j₀) with h | h
    · rw [h]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [h, mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  calc Real.exp (c * incrNorm B t ω)
      ≤ Real.exp (c * ∑ j, |v ω j|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (incrNorm_le_sum_abs B t ω) hc)
    _ ≤ Real.exp (K * |v ω j₀|) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hK, mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hc
    _ ≤ Real.exp (K * v ω j₀) + Real.exp (-K * v ω j₀) := hterm
    _ ≤ ∑ j, (Real.exp (K * v ω j) + Real.exp (-K * v ω j)) :=
        Finset.single_le_sum (f := fun j => Real.exp (K * v ω j) + Real.exp (-K * v ω j))
          (fun j _ => by positivity) (Finset.mem_univ j₀)

/-- A weight sequence of at most geometric growth is dominated termwise by the exponential
series, so its exponential generating function is bounded by `exp (r * x)`. -/
lemma summable_mul_pow_div_factorial_of_le_pow {w_fn : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w_fn n) {r : ℝ}
    (hwr : ∀ n, w_fn n ≤ r ^ n) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => w_fn n * (x ^ n / (n.factorial : ℝ))) ∧
      ∑' n : ℕ, w_fn n * (x ^ n / (n.factorial : ℝ)) ≤ Real.exp (r * x) := by
  have hexp : HasSum (fun n : ℕ => (r * x) ^ n / (n.factorial : ℝ)) (Real.exp (r * x)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (r * x)
  have hnn : ∀ n : ℕ, 0 ≤ w_fn n * (x ^ n / (n.factorial : ℝ)) := fun n =>
    mul_nonneg (hw0 n) (div_nonneg (pow_nonneg hx n) (Nat.cast_nonneg _))
  have hle : ∀ n : ℕ, w_fn n * (x ^ n / (n.factorial : ℝ)) ≤
      (r * x) ^ n / (n.factorial : ℝ) := fun n => by
    rw [mul_pow, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (hwr n)
      (div_nonneg (pow_nonneg hx n) (Nat.cast_nonneg _))
  have hsum := Summable.of_nonneg_of_le hnn hle hexp.summable
  exact ⟨hsum, (hsum.tsum_le_tsum hle hexp.summable).trans_eq hexp.tsum_eq⟩

/-- **Signature moment bound for geometric weights** (paper Proposition 12, chordal model):
if `0 ≤ w n ≤ r ^ n`, the weighted level series of `sig2OfBrownian B 0 t` converges pathwise
and has finite moments of every order `p ≥ 0`.

This is the provable form of `ProlongedBrownianSetup.factorial_moment_control`; the field as
currently stated (all-radius `R ^ n / n!` summability only) is false for Brownian drivers. -/
theorem sig2OfBrownian_geometric_moment_control (B : MultiBrownian Ω P d) {p : ℝ} (hp : 0 ≤ p)
    {w_fn : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w_fn n) {r : ℝ} (hwr : ∀ n, w_fn n ≤ r ^ n) (t : ℝ) :
    (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2OfBrownian B 0 t ω).levelNorm n)) ∧
      Integrable
        (fun ω => (∑' n : ℕ, w_fn n * (sig2OfBrownian B 0 t ω).levelNorm n) ^ p) P := by
  have hr : 0 ≤ r := by simpa using (hw0 1).trans (hwr 1)
  have hser := fun ω =>
    summable_mul_pow_div_factorial_of_le_pow hw0 hwr (incrNorm_nonneg B t ω)
  simp only [sig2OfBrownian_levelNorm_eq]
  refine ⟨fun ω => (hser ω).1, ?_⟩
  have hS0 : ∀ ω, 0 ≤ ∑' n : ℕ, w_fn n * (incrNorm B t ω ^ n / (n.factorial : ℝ)) :=
    fun ω => tsum_nonneg fun n => mul_nonneg (hw0 n)
      (div_nonneg (pow_nonneg (incrNorm_nonneg B t ω) n) (Nat.cast_nonneg _))
  have hmeas : Measurable
      (fun ω => ∑' n : ℕ, w_fn n * (incrNorm B t ω ^ n / (n.factorial : ℝ))) := by
    refine measurable_of_tendsto_metrizable
      (f := fun N ω => ∑ n ∈ Finset.range N,
        w_fn n * (incrNorm B t ω ^ n / (n.factorial : ℝ))) (fun N => ?_)
      (tendsto_pi_nhds.mpr fun ω => (hser ω).1.hasSum.tendsto_sum_nat)
    exact Finset.measurable_sum _ fun n _ =>
      (((measurable_incrNorm B t).pow_const n).div_const _).const_mul _
  refine (integrable_exp_mul_incrNorm B t (mul_nonneg hr hp)).mono'
    (hmeas.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hS0 ω) p)]
  calc (∑' n : ℕ, w_fn n * (incrNorm B t ω ^ n / (n.factorial : ℝ))) ^ p
      ≤ Real.exp (r * incrNorm B t ω) ^ p := Real.rpow_le_rpow (hS0 ω) (hser ω).2 hp
    _ = Real.exp (r * p * incrNorm B t ω) := by
        rw [← Real.exp_mul]
        ring_nf

/-! ### Sharpness: all-radius `R ^ n / n!` summability is not enough

The weights `gaussWeight a` below have exponential generating function `exp (a * x ^ 2)`, so
they are summable against `R ^ n / n!` at every radius, yet with `a = 1 / (2 t)` the weighted
level series of the signature is not integrable as soon as one Brownian coordinate exists. -/

/-- Weights with exponential generating function `x ↦ exp (a * x ^ 2)`:
`w (2 k) = a ^ k * (2 k)! / k!` and `w (2 k + 1) = 0`. -/
def gaussWeight (a : ℝ) (n : ℕ) : ℝ :=
  if Even n then a ^ (n / 2) * ((n.factorial : ℝ) / ((n / 2).factorial : ℝ)) else 0

lemma gaussWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ gaussWeight a n := by
  unfold gaussWeight
  split_ifs <;> positivity

lemma hasSum_gaussWeight (a x : ℝ) :
    HasSum (fun n : ℕ => gaussWeight a n * (x ^ n / (n.factorial : ℝ)))
      (Real.exp (a * x ^ 2)) := by
  have hexp : HasSum (fun k : ℕ => (a * x ^ 2) ^ k / (k.factorial : ℝ))
      (Real.exp (a * x ^ 2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (a * x ^ 2)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun _ _ h => by simpa using h
  refine (hinj.hasSum_iff fun n hn => ?_).mp ?_
  · have hodd : ¬ Even n := fun ⟨k, hk⟩ => hn ⟨k, by simp only; omega⟩
    simp [gaussWeight, hodd]
  · convert hexp using 1
    funext k
    have hk : ((2 * k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk' : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [Function.comp, gaussWeight, even_two_mul, ↓reduceIte,
      Nat.mul_div_cancel_left k two_pos]
    field_simp
    ring

/-- A centred Gaussian of variance `v > 0` does not integrate `exp (x ^ 2 / (2 v))`. -/
lemma not_integrable_exp_sq_gaussianReal {v : NNReal} (hv : v ≠ 0) :
    ¬ Integrable (fun x : ℝ => Real.exp ((2 * (v : ℝ))⁻¹ * x ^ 2))
      (ProbabilityTheory.gaussianReal 0 v) := by
  intro h
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff (ProbabilityTheory.measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => ProbabilityTheory.gaussianPDF_lt_top)] at h
  have hconst : (fun x : ℝ => Real.exp ((2 * (v : ℝ))⁻¹ * x ^ 2) *
      (ProbabilityTheory.gaussianPDF 0 v x).toReal) =
        fun _ => (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    funext x
    rw [ProbabilityTheory.toReal_gaussianPDF, ProbabilityTheory.gaussianPDFReal, mul_comm,
      mul_assoc, ← Real.exp_add]
    have h0 : -(x - 0) ^ 2 / (2 * (v : ℝ)) + (2 * (v : ℝ))⁻¹ * x ^ 2 = 0 := by ring
    rw [h0, Real.exp_zero, mul_one]
  rw [hconst, integrable_const_iff] at h
  rcases h with h | h
  · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)) h
  · exact measure_ne_top (volume : Measure ℝ) Set.univ Real.volume_univ

/-- **The all-radius hypothesis of `ProlongedBrownianSetup.factorial_moment_control` is too
weak.** For any `MultiBrownian` with at least one coordinate and any `t > 0` there are
nonnegative weights, summable against `R ^ n / n!` at every radius `R`, whose weighted level
series of `sig2OfBrownian B 0 t` is not integrable (already for `p = 1`). -/
theorem sig2OfBrownian_not_integrable_of_all_radius (B : MultiBrownian Ω P d) (i : Fin d)
    {t : ℝ} (ht : 0 < t) :
    ∃ w_fn : ℕ → ℝ, (∀ n, 0 ≤ w_fn n) ∧
      (∀ R : ℝ, 0 ≤ R → Summable (fun n : ℕ => w_fn n * (R ^ n / (n.factorial : ℝ)))) ∧
      ¬ Integrable
        (fun ω => (∑' n : ℕ, w_fn n * (sig2OfBrownian B 0 t ω).levelNorm n) ^ (1 : ℝ)) P := by
  set v : NNReal := Real.toNNReal t with hv_def
  have hv : v ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  refine ⟨gaussWeight (2 * (v : ℝ))⁻¹, gaussWeight_nonneg (by positivity),
    fun R _ => (hasSum_gaussWeight _ R).summable, fun hint => ?_⟩
  simp only [sig2OfBrownian_levelNorm_eq, (hasSum_gaussWeight _ _).tsum_eq,
    Real.rpow_one] at hint
  have hlaw := (B.isBrownian i).toIsPreBrownianReal.hasLaw_eval v
  have hW : Integrable (fun ω => Real.exp ((2 * (v : ℝ))⁻¹ * (B.Wnn v ω i) ^ 2)) P := by
    refine hint.mono' (((B.Wnn_meas v i).pow_const 2).const_mul _).exp.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [incrNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hWeq : MultiBrownian.W B t ω i = B.Wnn v ω i := rfl
    have hsingle := Finset.single_le_sum
      (f := fun j => (MultiBrownian.wAug B t ω j - MultiBrownian.wAug B 0 ω j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩)
    simpa only [MultiBrownian.wAug_space, MultiBrownian.W_zero, sub_zero, hWeq] using hsingle
  have hmap : Integrable (fun x : ℝ => Real.exp ((2 * (v : ℝ))⁻¹ * x ^ 2))
      (P.map (fun ω => B.Wnn v ω i)) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable (by fun_prop))
      hlaw.aemeasurable).mpr hW
  rw [hlaw.map_eq] at hmap
  exact not_integrable_exp_sq_gaussianReal hv hmap

/-- Build `ProlongedBrownianSetup` from multi-dimensional Brownian motion. -/
def prolongedBrownianSetup_of_brownian {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ProlongedBrownianSetup Ω P d T where
  hT_pos := hT
  W := MultiBrownian.W B
  W_zero := MultiBrownian.W_zero B
  W_meas := MultiBrownian.W_meas B
  sig2 := sig2OfBrownian B
  sig_meas := sig2OfBrownian_meas B
  sig2_empty := sig2OfBrownian_empty B
  sig2_time := sig2OfBrownian_time B
  sig2_space := sig2OfBrownian_space B
  sig_adapted_to_W := sig2OfBrownian_adapted B
  stratonovich_chen := fun s t _ _ _ ω => sig2OfBrownian_chen B s t ω
  stratonovich_shuffle := fun t _ _ I J ω => sig2OfBrownian_shuffle B t I J ω
  factorial_moment_control := fun p hp w_fn hw0 ⟨r, hwr⟩ t _ _ => by
    have := sig2OfBrownian_geometric_moment_control B (zero_le_one.trans hp) hw0 hwr t
    exact this

end SignatureVolatility
