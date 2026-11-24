module

public import SignatureVolatility.MemTw
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential


/-!
# C1. Combinatorial core of the Girsanov–Fawcett / Hermite expansion

Sorry-free so far: monic Hermite polynomials
`H_k(z; t) := ∫ (z + I √t x)^k ∂γ` of variance `t` (integral representation,
binomial expansion, holomorphy, and the Gaussian bound), Fawcett blocks and
concatenative parse counts `c(I; a, k, b)`, the multinomial recurrence, and
the definitions of the word polynomials `P_{I,t}` and the generating function
`G(z) = ∑_I φ_I P_{I,t}(z)`.

Still to prove in this module (no `sorry` placeholders; lemmas will be added
as they land): the counting identity `∑_{|I|=n} c = (a+k+b)! / (a! k! ∏ b_j!)`,
the bound `∑_I ‖P_{I,t}(z)‖ ≤ 2 exp(t + (d+1)t/2) e^{‖z‖}`, and that `G` is
entire of exponential type `≤ 1` for `φ ∈ T_w`.

The Girsanov–Fawcett identification `P_{I,t}(x) = E[Ŵ_t^I | W_t = x]` lives in
`GirsanovFawcett`; the transfer to `f` (Pillar C) lives in `EntireTransfer`.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Nat ENNReal NNReal

namespace SignatureVolatility

open ExtTensorAlgebra

/-! ### Monic Hermite polynomials of variance `t` -/

/-- Monic (probabilists') Hermite polynomial of degree `k` and variance `t`,
via the Gaussian integral `H_k(z; t) = E[(z + I √t G)^k]` with `G ∼ N(0,1)`.
For `t < 0` Lean's `Real.sqrt` vanishes, so the formula is only used at `t ≥ 0`. -/
def monicHermite (k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k ∂gaussianReal 0 1

private lemma integrable_abs_pow_gaussian (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal (0 : ℝ) 1) := by
  have hLp : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) (k : ℝ≥0∞) (ENNReal.natCast_ne_top k)
  have hint := hLp.integrable_norm_rpow'
  simpa [Real.norm_eq_abs, ENNReal.toReal_natCast] using hint

private lemma pow_add_le_two_mul_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ (2 : ℝ) ^ k * (a ^ k + b ^ k) := by
  have hmax : a + b ≤ 2 * max a b := by
    simpa [two_mul] using add_le_add (le_max_left a b) (le_max_right a b)
  have h1 : (a + b) ^ k ≤ (2 * max a b) ^ k :=
    pow_le_pow_left₀ (add_nonneg ha hb) hmax k
  have h3 : (max a b) ^ k ≤ a ^ k + b ^ k := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (pow_nonneg ha k)
    · rw [max_eq_left hba]
      exact le_add_of_nonneg_right (pow_nonneg hb k)
  calc (a + b) ^ k
      ≤ (2 * max a b) ^ k := h1
    _ = (2 : ℝ) ^ k * (max a b) ^ k := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ k * (a ^ k + b ^ k) :=
        mul_le_mul_of_nonneg_left h3 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)

private lemma norm_I_mul_sqrt (t : ℝ) :
    ‖I * (Real.sqrt t : ℂ)‖ = Real.sqrt t := by
  have hs : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
  rw [norm_mul, norm_I, one_mul, hs]

private lemma monicHermite_integrand_bound (k : ℕ) (t : ℝ) (z : ℂ) (x : ℝ) :
    ‖(z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k‖ ≤
      (2 : ℝ) ^ k * (‖z‖ ^ k + (Real.sqrt t) ^ k * |x| ^ k) := by
  set c : ℂ := I * (Real.sqrt t : ℂ)
  have hadd : ‖z + c * (x : ℂ)‖ ≤ ‖z‖ + ‖c‖ * |x| := by
    calc ‖z + c * (x : ℂ)‖
        ≤ ‖z‖ + ‖c * (x : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖c‖ * ‖(x : ℂ)‖ := by rw [norm_mul]
      _ = ‖z‖ + ‖c‖ * |x| := by simp [Complex.norm_real, Real.norm_eq_abs]
  have hc : ‖c‖ = Real.sqrt t := norm_I_mul_sqrt t
  have hnn1 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖c‖ * |x| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hineq := pow_add_le_two_mul_pow hnn1 hnn2 k
  have hcs : (‖c‖ * |x|) ^ k = (Real.sqrt t) ^ k * |x| ^ k := by
    rw [mul_pow, hc]
  calc ‖(z + c * (x : ℂ)) ^ k‖
      = ‖z + c * (x : ℂ)‖ ^ k := norm_pow _ _
    _ ≤ (‖z‖ + ‖c‖ * |x|) ^ k := pow_le_pow_left₀ (norm_nonneg _) hadd k
    _ ≤ (2 : ℝ) ^ k * (‖z‖ ^ k + (‖c‖ * |x|) ^ k) := hineq
    _ = (2 : ℝ) ^ k * (‖z‖ ^ k + (Real.sqrt t) ^ k * |x| ^ k) := by rw [hcs]

private lemma integrable_two_pow_bound (k : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => (2 : ℝ) ^ k * (‖z‖ ^ k + (Real.sqrt t) ^ k * |x| ^ k))
      (gaussianReal 0 1) := by
  let f : ℝ → ℝ := fun _ => (2 : ℝ) ^ k * ‖z‖ ^ k
  let g : ℝ → ℝ := fun x => ((2 : ℝ) ^ k * (Real.sqrt t) ^ k) * |x| ^ k
  have hf : Integrable f (gaussianReal 0 1) := integrable_const _
  have hg : Integrable g (gaussianReal 0 1) :=
    (integrable_abs_pow_gaussian k).const_mul _
  have heq : (fun x : ℝ => (2 : ℝ) ^ k * (‖z‖ ^ k + (Real.sqrt t) ^ k * |x| ^ k)) = f + g := by
    funext x; simp [f, g]; ring
  simpa [heq] using hf.add hg

lemma integrable_monicHermite_integrand (k : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => (z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k)
      (gaussianReal 0 1) := by
  have hbd := integrable_two_pow_bound k t z
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k) (gaussianReal 0 1) := by
    have hcont : Continuous
        (fun x : ℝ => (z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k) := by
      continuity
    exact hcont.aestronglyMeasurable
  exact Integrable.mono' hbd hmeas (ae_of_all _ (monicHermite_integrand_bound k t z))

private lemma integrable_ofReal_pow (m : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 1) := by
  have hbd : Integrable (fun x : ℝ => |x| ^ m) (gaussianReal 0 1) :=
    integrable_abs_pow_gaussian m
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 1) :=
    (Complex.continuous_ofReal.pow m).aestronglyMeasurable
  refine Integrable.mono' hbd hmeas (ae_of_all _ fun x => ?_)
  simp [Complex.norm_real, Real.norm_eq_abs, norm_pow]

lemma monicHermite_eq_sum (k : ℕ) (t : ℝ) (z : ℂ) :
    monicHermite k t z =
      ∑ m ∈ Finset.range (k + 1),
        (k.choose m : ℂ) * z ^ (k - m) * (I * (Real.sqrt t : ℂ)) ^ m *
          ∫ x : ℝ, (x : ℂ) ^ m ∂gaussianReal 0 1 := by
  set c : ℂ := I * (Real.sqrt t : ℂ)
  have hfun :
      (fun x : ℝ => (z + c * (x : ℂ)) ^ k) =
        fun x : ℝ => ∑ m ∈ Finset.range (k + 1),
          (k.choose m : ℂ) * z ^ (k - m) * c ^ m * (x : ℂ) ^ m := by
    ext x
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mul_pow]
    ring
  unfold monicHermite
  change (∫ x : ℝ, (z + c * (x : ℂ)) ^ k ∂gaussianReal 0 1) = _
  rw [hfun]
  have hint : ∀ m ∈ Finset.range (k + 1),
      Integrable (fun x : ℝ =>
        (k.choose m : ℂ) * z ^ (k - m) * c ^ m * (x : ℂ) ^ m) (gaussianReal 0 1) :=
    fun m _ => (integrable_ofReal_pow m).const_mul _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul]

lemma monicHermite_differentiable (k : ℕ) (t : ℝ) :
    Differentiable ℂ (monicHermite k t) := by
  have hfun : monicHermite k t = fun z =>
      ∑ m ∈ Finset.range (k + 1),
        (k.choose m : ℂ) * z ^ (k - m) * (I * (Real.sqrt t : ℂ)) ^ m *
          ∫ x : ℝ, (x : ℂ) ^ m ∂gaussianReal 0 1 := by
    funext z
    exact monicHermite_eq_sum k t z
  rw [hfun]
  refine Differentiable.fun_sum fun m _ => ?_
  exact (((differentiable_const _).mul (differentiable_id.pow _)).mul
    (differentiable_const _)).mul (differentiable_const _)

private lemma integrable_monicHermite_norm_bound (k : ℕ) (t : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ => (‖z‖ + Real.sqrt t * |x|) ^ k) (gaussianReal 0 1) := by
  have hbd := integrable_two_pow_bound k t z
  have hle : ∀ x : ℝ,
      ‖(‖z‖ + Real.sqrt t * |x|) ^ k‖ ≤
        (2 : ℝ) ^ k * (‖z‖ ^ k + (Real.sqrt t) ^ k * |x| ^ k) := fun x => by
    have hnn : 0 ≤ (‖z‖ + Real.sqrt t * |x|) ^ k :=
      pow_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg t) (abs_nonneg _))) k
    have hpow := pow_add_le_two_mul_pow (norm_nonneg z)
      (mul_nonneg (Real.sqrt_nonneg t) (abs_nonneg x)) k
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    simpa [mul_pow] using hpow
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => (‖z‖ + Real.sqrt t * |x|) ^ k) (gaussianReal 0 1) := by
    have hcont : Continuous (fun x : ℝ => (‖z‖ + Real.sqrt t * |x|) ^ k) := by
      continuity
    exact hcont.aestronglyMeasurable
  exact Integrable.mono' hbd hmeas' (ae_of_all _ hle)

lemma monicHermite_bound (k : ℕ) {t : ℝ} (_ht : 0 ≤ t) (z : ℂ) :
    ‖monicHermite k t z‖ ≤
      ∫ x : ℝ, (‖z‖ + Real.sqrt t * |x|) ^ k ∂gaussianReal 0 1 := by
  have hint := integrable_monicHermite_integrand k t z
  have hnorm :=
    (norm_integral_le_integral_norm (μ := gaussianReal 0 1)
      (fun x : ℝ => (z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k))
  have hpoint : ∀ x : ℝ,
      ‖(z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k‖ ≤
        (‖z‖ + Real.sqrt t * |x|) ^ k := fun x => by
    have hadd : ‖z + I * (Real.sqrt t : ℂ) * (x : ℂ)‖ ≤ ‖z‖ + Real.sqrt t * |x| := by
      have hc := norm_I_mul_sqrt t
      calc ‖z + I * (Real.sqrt t : ℂ) * (x : ℂ)‖
          ≤ ‖z‖ + ‖I * (Real.sqrt t : ℂ) * (x : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ + ‖I * (Real.sqrt t : ℂ)‖ * ‖(x : ℂ)‖ := by rw [norm_mul]
        _ = ‖z‖ + Real.sqrt t * |x| := by
            rw [hc, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(z + I * (Real.sqrt t : ℂ) * (x : ℂ)) ^ k‖
        = ‖z + I * (Real.sqrt t : ℂ) * (x : ℂ)‖ ^ k := norm_pow _ _
      _ ≤ (‖z‖ + Real.sqrt t * |x|) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hadd k
  have hmono :=
    integral_mono hint.norm (integrable_monicHermite_norm_bound k t z) hpoint
  exact hnorm.trans hmono


/-! ### Fawcett blocks and concatenative parse counts -/

/-- The three generators appearing in the tilted Fawcett exponential
`exp_⊗(t(e_0 + μ e_1 + ½ ∑_j e_{jj}))`: a time letter, a singleton first-space
letter, or a repeated space-letter pair. -/
inductive FawcettBlock (d : ℕ) where
  | time : FawcettBlock d
  | first : FawcettBlock d
  | pair (j : Fin d) : FawcettBlock d
deriving DecidableEq

def FawcettBlock.equivSum (d : ℕ) : FawcettBlock d ≃ Unit ⊕ Unit ⊕ Fin d where
  toFun
    | .time => .inl ()
    | .first => .inr (.inl ())
    | .pair j => .inr (.inr j)
  invFun
    | .inl () => .time
    | .inr (.inl ()) => .first
    | .inr (.inr j) => .pair j
  left_inv
    | .time => rfl
    | .first => rfl
    | .pair _ => rfl
  right_inv
    | .inl () => rfl
    | .inr (.inl ()) => rfl
    | .inr (.inr _) => rfl

instance (d : ℕ) : Fintype (FawcettBlock d) :=
  Fintype.ofEquiv _ (FawcettBlock.equivSum d).symm

/-- Concatenative image of a block as a word on `d+1` letters (time is `0`).
The first space letter is `(⟨0, hd⟩ : Fin d).succ`; this module does not
introduce a public `firstSpace` name. -/
def FawcettBlock.toWord {d : ℕ} (hd : 0 < d) : FawcettBlock d → Word (d + 1)
  | .time => [0]
  | .first => [(⟨0, hd⟩ : Fin d).succ]
  | .pair j => [j.succ, j.succ]

def FawcettBlock.weight {d : ℕ} : FawcettBlock d → ℕ
  | .pair _ => 2
  | _ => 1

lemma FawcettBlock.toWord_length {d : ℕ} (hd : 0 < d) (x : FawcettBlock d) :
    (x.toWord hd).length = x.weight := by
  cases x <;> rfl

/-- Multiplicities of each block type in a parsing. -/
def blockCount (d : ℕ) (a k : ℕ) (b : Fin d → ℕ) : FawcettBlock d → ℕ
  | .time => a
  | .first => k
  | .pair j => b j

lemma blockCount_sum (d : ℕ) (a k : ℕ) (b : Fin d → ℕ) :
    ∑ x : FawcettBlock d, blockCount d a k b x = a + k + ∑ j, b j := by
  rw [Fintype.sum_equiv (FawcettBlock.equivSum d) (blockCount d a k b)
      (fun y => blockCount d a k b ((FawcettBlock.equivSum d).symm y))
      (fun _ => by simp)]
  simp [FawcettBlock.equivSum, blockCount, add_assoc]

/-- Concatenation of the block-words of a finite sequence of blocks. -/
def concatBlocks {d : ℕ} (hd : 0 < d) {m : ℕ} (f : Fin m → FawcettBlock d) :
    Word (d + 1) :=
  (List.ofFn f).flatMap (FawcettBlock.toWord hd)

lemma list_sum_ofFn {α : Type*} [AddCommMonoid α] {m : ℕ} (g : Fin m → α) :
    (List.ofFn g).sum = ∑ i : Fin m, g i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ, ih]

lemma concatBlocks_length {d : ℕ} (hd : 0 < d) {m : ℕ}
    (f : Fin m → FawcettBlock d) :
    (concatBlocks hd f).length = ∑ i : Fin m, (f i).weight := by
  classical
  unfold concatBlocks
  rw [List.length_flatMap]
  have hmap :
      (List.ofFn f).map (fun x => (FawcettBlock.toWord hd x).length) =
        (List.ofFn f).map (fun x => x.weight) :=
    List.map_congr_left fun x _ => FawcettBlock.toWord_length hd x
  rw [hmap, List.map_ofFn, list_sum_ofFn]
  rfl

/-- Functions `Fin m → FawcettBlock d` with prescribed block counts, where
`m = a + k + ∑ b`. -/
def parseFuns (d : ℕ) (a k : ℕ) (b : Fin d → ℕ) :
    Finset (Fin (a + k + ∑ j, b j) → FawcettBlock d) :=
  Finset.univ.filter fun f =>
    ∀ x, (Finset.univ.filter (fun i => f i = x)).card = blockCount d a k b x

/-- Number of concatenative parsings of the word `I` into `a` copies of `[0]`,
`k` copies of the first space letter, and `b_j` copies of `[j,j]`. -/
def parseCount (d : ℕ) (hd : 0 < d) (I : Word (d + 1)) (a k : ℕ)
    (b : Fin d → ℕ) : ℕ :=
  ((parseFuns d a k b).filter (fun f => concatBlocks hd f = I)).card

lemma sum_univ_succ_apply {n : ℕ} (c : Fin (n + 1) → ℕ) :
    ∑ x : Fin (n + 1), c x = c 0 + ∑ x : Fin n, c x.succ := by
  rw [Fin.univ_succ, Finset.sum_cons, Finset.sum_map]
  rfl

lemma multinomial_univ_succ {n : ℕ} (c : Fin (n + 1) → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (n + 1))) c =
      (∑ x : Fin (n + 1), c x).choose (c 0) *
        Nat.multinomial (Finset.univ : Finset (Fin n)) (fun x => c x.succ) := by
  have hLHS :
      Nat.multinomial (Finset.univ : Finset (Fin (n + 1))) c =
        (c 0 + ∑ x : Fin n, c x.succ).choose (c 0) *
          Nat.multinomial (Finset.univ : Finset (Fin n)) (fun x => c x.succ) := by
    rw [Fin.univ_succ, Nat.multinomial_cons]
    congr 1
    · rw [Finset.sum_map]; rfl
    · unfold Nat.multinomial
      rw [Finset.sum_map, Finset.prod_map]
      rfl
  rw [hLHS, sum_univ_succ_apply]


/-! ### Word polynomials `P_{I,t}` and the generating function `G` (definitions) -/

/-- Finite index set of Fawcett count triples `(a, k, b)` with `a + k + 2 ∑ b_j = n`. -/
def fawcettIndexSet (d n : ℕ) : Finset (ℕ × ℕ × (Fin d → ℕ)) :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      (Fintype.piFinset fun _ : Fin d => Finset.range (n + 1))).filter
    fun p => p.1 + p.2.1 + 2 * ∑ j, p.2.2 j = n)

/-- Carbon's word polynomial
`P_{I,t}(z) = ∑_{a+k+2b=|I|} c(I;a,k,b) t^{a+b} / (2^b (a+k+b)!) H_k(z;t)`. -/
def fawcettPoly {d : ℕ} (hd : 0 < d) (I : Word (d + 1)) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ fawcettIndexSet d I.length,
    let a := p.1
    let k := p.2.1
    let b := p.2.2
    let s := ∑ j, b j
    (parseCount d hd I a k b : ℂ) * (t : ℂ) ^ (a + s) /
      ((2 : ℂ) ^ s * ((a + k + s).factorial : ℂ)) * monicHermite k t z

/-- Generating function `G(z) = ∑_n ∑_{|I|=n} φ_I P_{I,t}(z)`. Entire of type `≤ 1` is
proved later from the missing counting identity and sum bound. -/
def fawcettEntire {d : ℕ} (hd : 0 < d) (phi : ExtTensorAlgebra (d + 1))
    (t : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * fawcettPoly hd I t z

end SignatureVolatility
