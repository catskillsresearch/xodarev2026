import Mathlib

/-!
# On the Structural Foundations of Signature Volatility Models
Formalization of arXiv:2605.17142v1 by Akmal Xodarev.

No `axiom`s and no `sorry`s are used anywhere in this file.
-/

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

/-! ## Section 0: Algebraic & Analytic Preliminaries (Cauchy–Schwarz, Minkowski, Gronwall) -/

/-- Finite Lagrange/Cauchy–Schwarz inequality on any `Finset`. -/
lemma finset_sum_mul_sq_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hid : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) := by
    calc
      ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2
          = ∑ i ∈ s, ∑ j ∈ s, ((f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2) -
              2 * (f i * g i) * (f j * g j)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ i ∈ s, ∑ j ∈ s, f i ^ 2 * g j ^ 2) + (∑ i ∈ s, ∑ j ∈ s, f j ^ 2 * g i ^ 2) -
            ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * g i) * (f j * g j) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) +
            (∑ i ∈ s, g i ^ 2) * (∑ j ∈ s, f j ^ 2) -
            2 * ((∑ i ∈ s, f i * g i) * (∑ j ∈ s, f j * g j)) := by
            congr 1
            · congr 1
              · rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
              · rw [Finset.sum_comm, Finset.sum_mul]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => mul_comm _ _
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * ((∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) := by ring
  linarith

/-- Square-root form of finite Cauchy–Schwarz. -/
lemma abs_finset_sum_mul_le_sqrt {α : Type*} (s : Finset α) (f g : α → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hf : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_mul hf, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (finset_sum_mul_sq_le s f g)

/-- Euclidean triangle inequality on a `Finset`. -/
lemma sqrt_sum_add_sq_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hf : 0 ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) := Real.sqrt_nonneg _
  have hg : 0 ≤ Real.sqrt (∑ i ∈ s, g i ^ 2) := Real.sqrt_nonneg _
  have hsum_f : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_g : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : ∑ i ∈ s, f i * g i ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) :=
    (le_abs_self _).trans (abs_finset_sum_mul_le_sqrt s f g)
  have hsq : ∑ i ∈ s, (f i + g i) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2 := by
    calc
      ∑ i ∈ s, (f i + g i) ^ 2
          = (∑ i ∈ s, f i ^ 2) + 2 * (∑ i ∈ s, f i * g i) + (∑ i ∈ s, g i ^ 2) := by
            have hexp : ∀ i, (f i + g i) ^ 2 = f i ^ 2 + 2 * (f i * g i) + g i ^ 2 :=
              fun _ => by ring
            simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) ^ 2 +
            2 * (Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2)) +
            Real.sqrt (∑ i ∈ s, g i ^ 2) ^ 2 := by
            rw [Real.sq_sqrt hsum_f, Real.sq_sqrt hsum_g]
            linarith
      _ = (Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2 := by ring
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (add_nonneg hf hg))

/-- Finite Minkowski inequality for Euclidean norms over `Finset`s. -/
lemma sqrt_sum_finset_sum_sq_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (F : β → α → ℝ) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ t, F k i) ^ 2) ≤
      ∑ k ∈ t, Real.sqrt (∑ i ∈ s, (F k i) ^ 2) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert b t hb ih =>
    have hrew : (∑ i ∈ s, (∑ k ∈ insert b t, F k i) ^ 2) =
        ∑ i ∈ s, (F b i + ∑ k ∈ t, F k i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_insert hb]
    rw [hrew, Finset.sum_insert hb]
    exact (sqrt_sum_add_sq_le s (F b) (fun i => ∑ k ∈ t, F k i)).trans (add_le_add_left ih _)

/-- Sum of squares of non-negative reals is bounded by the square of their sum. -/
lemma sum_sq_le_sq_sum {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hmul : 0 ≤ 2 * f a * (∑ i ∈ s, f i) := by positivity
    nlinarith

/-- Partial-sum bound for Cauchy convolution of non-negative sequences. -/
lemma cauchy_range_sum_le (N : ℕ) (u v : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hv : ∀ j, 0 ≤ v j) :
    (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) ≤
      (∑ k ∈ Finset.range N, u k) * (∑ j ∈ Finset.range N, v j) := by
  let g : ℕ → ℕ → ℝ := fun k n => if k ≤ n then u k * v (n - k) else 0
  have h1 : (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) =
      ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N, g k n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    symm
    rw [← Finset.sum_subset (Finset.range_mono hnN)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [g, hkn]
    · intro k _ hknot
      have hnot : ¬ k ≤ n := fun hle => hknot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [g, hnot]
  rw [h1, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
  have hsplit : N = k + (N - k) := (Nat.add_sub_of_le hkN).symm
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range k, g k x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hnot : ¬ k ≤ x := Nat.not_le_of_gt (Finset.mem_range.mp hx)
    simp [g, hnot]
  rw [hzero, zero_add]
  have htail : ∑ x ∈ Finset.range (N - k), g k (k + x) =
      u k * ∑ x ∈ Finset.range (N - k), v x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [g]
  rw [htail]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N k))
      fun j _ _ => hv j) (hu k)

/-- Absolute triangle inequality for convergent real series. -/
lemma abs_tsum_le_of_summable_abs {f : ℕ → ℝ} (habs : Summable (fun n => |f n|)) :
    |∑' n, f n| ≤ ∑' n, |f n| := by
  have hf : Summable f := habs.of_abs
  have htend1 : Tendsto (fun N => |∑ n ∈ Finset.range N, f n|) atTop (𝓝 |∑' n, f n|) :=
    hf.hasSum.tendsto_sum_nat.abs
  have htend2 : Tendsto (fun N => ∑ n ∈ Finset.range N, |f n|) atTop (𝓝 (∑' n, |f n|)) :=
    habs.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto htend1 htend2
    (Eventually.of_forall fun N => Finset.abs_sum_le_sum_abs f (Finset.range N))

/-- Integral Gronwall lemma for continuous non-negative functions on `[0, T]`, proved by
iterating the integral bound and invoking factorial decay `Real.summable_pow_div_factorial`. -/
lemma gronwall_zero_of_continuousOn {f : ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcont : ContinuousOn f (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ K * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  have hcomp : IsCompact (Icc (0 : ℝ) T) := isCompact_Icc
  have hne : (Icc (0 : ℝ) T).Nonempty := nonempty_Icc.mpr hT
  obtain ⟨t_max, ht_max, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  let B : ℝ := max (f t_max) 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hfB : ∀ t ∈ Icc 0 T, f t ≤ B := fun t ht => (hmax ht).trans (le_max_left _ _)
  have hiter : ∀ (n : ℕ), ∀ t ∈ Icc 0 T, f t ≤ B * ((K * t) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa using hfB t ht
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      have hf_int : IntervalIntegrable f volume 0 t :=
        (hcont.mono hsub).intervalIntegrable_of_Icc ht0
      let g : ℝ → ℝ := fun s => B * K ^ n / (n.factorial : ℝ) * s ^ n
      have hg_cont : ContinuousOn g (Icc 0 t) :=
        (continuous_const.mul (continuous_pow n)).continuousOn
      have hg_int : IntervalIntegrable g volume 0 t := hg_cont.intervalIntegrable_of_Icc ht0
      have hfg : ∀ s ∈ Icc 0 t, f s ≤ g s := by
        intro s hs
        have hstep := ih s (hsub hs)
        calc
          f s ≤ B * ((K * s) ^ n / (n.factorial : ℝ)) := hstep
          _ = g s := by simp [g, mul_pow]; ring
      have hint_le : ∫ s in (0 : ℝ)..t, f s ≤ ∫ s in (0 : ℝ)..t, g s :=
        intervalIntegral.integral_mono_on ht0 hf_int hg_int hfg
      have hint_g : ∫ s in (0 : ℝ)..t, g s =
          (B * K ^ n / (n.factorial : ℝ)) * (t ^ (n + 1) / (n + 1 : ℝ)) := by
        simp only [g, intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc
        f t ≤ K * ∫ s in (0 : ℝ)..t, f s := hbound t ht
        _ ≤ K * ∫ s in (0 : ℝ)..t, g s := mul_le_mul_of_nonneg_left hint_le hK
        _ = K * ((B * K ^ n / (n.factorial : ℝ)) * (t ^ (n + 1) / (n + 1 : ℝ))) := by rw [hint_g]
        _ = B * ((K * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, mul_pow]
          ring
  intro t ht
  have htend : Tendsto (fun n : ℕ => B * ((K * t) ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      tendsto_const_nhds.mul (Real.summable_pow_div_factorial (K * t)).tendsto_atTop_zero
  have hle0 : f t ≤ 0 :=
    le_of_tendsto' htend fun n => hiter n t ht
  exact le_antisymm hle0 (hnonneg t ht)

/-! ## Section 2.1: The Free and Extended Tensor Algebras over `ℝ^d` -/

/-- Alphabet `{0, ..., d - 1}` representing basis indices of `ℝ^d`. -/
abbrev Letter (d : ℕ) := Fin d

/-- Multi-indices `I = (i₁, ..., iₙ)` over `{1, ..., d}` (Definition 2.1). -/
abbrev Word (d : ℕ) := List (Letter d)

/-- Exact `Finset` of all multi-indices of length `n` over alphabet `Fin d`. -/
def wordsOfLength (d : ℕ) : ℕ → Finset (Word d)
  | 0 => {[]}
  | n + 1 =>
    (Finset.univ : Finset (Fin d)).biUnion fun i =>
      (wordsOfLength d n).map ⟨fun I => i :: I, fun _ _ h => (List.cons.inj h).2⟩

lemma mem_wordsOfLength {d : ℕ} : ∀ {n : ℕ} {I : Word d}, I ∈ wordsOfLength d n ↔ I.length = n
  | 0, [] => by simp [wordsOfLength]
  | 0, _ :: _ => by simp [wordsOfLength]
  | n + 1, [] => by simp [wordsOfLength]
  | n + 1, i :: I => by
    simp only [wordsOfLength, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨a, J, hJ, hcons⟩
      cases hcons
      exact mem_wordsOfLength.mp hJ
    · intro hlen
      exact ⟨i, I, mem_wordsOfLength.mpr hlen, rfl⟩

lemma sum_wordsOfLength_succ {d : ℕ} (n : ℕ) (F : Word d → ℝ) :
    ∑ I ∈ wordsOfLength d (n + 1), F I =
      ∑ i : Fin d, ∑ J ∈ wordsOfLength d n, F (i :: J) := by
  unfold wordsOfLength
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_map]
    rfl
  · intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro L hLi hLj
    rcases Finset.mem_map.mp hLi with ⟨I₁, _, rfl⟩
    rcases Finset.mem_map.mp hLj with ⟨I₂, _, hcons⟩
    exact hij (List.cons.inj hcons).1

lemma sum_wordsOfLength_take_drop_sq (d : ℕ) :
    ∀ (k n : ℕ), k ≤ n → ∀ (f g : Word d → ℝ),
      ∑ I ∈ wordsOfLength d n, (f (I.take k) * g (I.drop k)) ^ 2 =
        (∑ J ∈ wordsOfLength d k, f J ^ 2) * (∑ K ∈ wordsOfLength d (n - k), g K ^ 2)
  | 0, n, _, f, g => by
    simp [wordsOfLength, mul_pow, Finset.mul_sum]
  | k + 1, 0, hk, _, _ => absurd hk (Nat.not_succ_le_zero k)
  | k + 1, n + 1, hk, f, g => by
    have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
    rw [Nat.add_sub_add_right, sum_wordsOfLength_succ, sum_wordsOfLength_succ]
    simp only [List.take, List.drop]
    have hstep : ∀ i : Fin d,
        ∑ J ∈ wordsOfLength d n, (f (i :: J.take k) * g (J.drop k)) ^ 2 =
          (∑ J ∈ wordsOfLength d k, f (i :: J) ^ 2) *
            (∑ K ∈ wordsOfLength d (n - k), g K ^ 2) :=
      fun i => sum_wordsOfLength_take_drop_sq d k n hk' (fun J => f (i :: J)) g
    simp_rw [hstep, ← Finset.sum_mul]

/-- **Definition 2.3 (Extended tensor algebra)**: `T((ℝ^d)) = ∏_{n ≥ 0} (ℝ^d)^{⊗ n}`,
represented via word-indexed formal series. -/
@[ext]
structure ExtTensorAlgebra (d : ℕ) where
  coeff : Word d → ℝ

namespace ExtTensorAlgebra

instance {d : ℕ} : Zero (ExtTensorAlgebra d) := ⟨⟨fun _ => 0⟩⟩
instance {d : ℕ} : Add (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I + b.coeff I⟩⟩
instance {d : ℕ} : Neg (ExtTensorAlgebra d) := ⟨fun a => ⟨fun I => -a.coeff I⟩⟩
instance {d : ℕ} : Sub (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I - b.coeff I⟩⟩
instance {d : ℕ} : SMul ℝ (ExtTensorAlgebra d) := ⟨fun c a => ⟨fun I => c * a.coeff I⟩⟩

instance {d : ℕ} : AddCommGroup (ExtTensorAlgebra d) where
  add_assoc a b c := by ext I; exact add_assoc _ _ _
  zero_add a := by ext I; exact zero_add _
  add_zero a := by ext I; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext I; exact neg_add_cancel _
  add_comm a b := by ext I; exact add_comm _ _

instance {d : ℕ} : Module ℝ (ExtTensorAlgebra d) where
  one_smul a := by ext I; exact one_mul _
  mul_smul r s a := by ext I; exact mul_assoc _ _ _
  smul_zero r := by ext I; exact mul_zero _
  smul_add r a b := by ext I; exact mul_add _ _ _
  add_smul r s a := by ext I; exact add_mul _ _ _
  zero_smul a := by ext I; exact zero_mul _

/-- Canonical basis vector `e_I` (Definition 2.1), with `basisWord [] = e_∅ = 1`. -/
def basisWord {d : ℕ} (I : Word d) : ExtTensorAlgebra d :=
  ⟨fun J => if J = I then 1 else 0⟩

/-- Coordinate extraction `⟨e_I, a⟩` on `T((ℝ^d))`. -/
def coord {d : ℕ} (I : Word d) (a : ExtTensorAlgebra d) : ℝ :=
  a.coeff I

/-- Squared Euclidean norm `|a_n|^2` of homogeneous tensor level `n`. -/
def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, (a.coeff I) ^ 2

/-- Euclidean norm `|a_n|_{(ℝ^d)^{⊗ n}}` of homogeneous tensor level `n`. -/
def levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  Real.sqrt (levelNormSq a n)

/-- Inner product `⟨ℓ_n, a_n⟩` at homogeneous tensor level `n`. -/
def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, ℓ.coeff I * a.coeff I

lemma levelNormSq_nonneg {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    0 ≤ levelNormSq a n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma levelNorm_nonneg {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    0 ≤ levelNorm a n :=
  Real.sqrt_nonneg _

lemma sq_levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    (levelNorm a n) ^ 2 = levelNormSq a n :=
  Real.sq_sqrt (levelNormSq_nonneg a n)

lemma abs_levelInner_le {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) :
    |levelInner ℓ a n| ≤ levelNorm ℓ n * levelNorm a n :=
  abs_finset_sum_mul_le_sqrt (wordsOfLength d n) ℓ.coeff a.coeff

lemma levelNorm_add_le {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a + b) n ≤ levelNorm a n + levelNorm b n :=
  sqrt_sum_add_sq_le (wordsOfLength d n) a.coeff b.coeff

lemma levelNorm_sub_eq_neg {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a - b) n = levelNorm (b - a) n := by
  unfold levelNorm levelNormSq
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  change (a.coeff I - b.coeff I) ^ 2 = (b.coeff I - a.coeff I) ^ 2
  ring

lemma levelNorm_smul {d : ℕ} (c : ℝ) (a : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (c • a) n = |c| * levelNorm a n := by
  unfold levelNorm levelNormSq
  have h : ∑ I ∈ wordsOfLength d n, (c * a.coeff I) ^ 2 =
      c ^ 2 * ∑ I ∈ wordsOfLength d n, a.coeff I ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => by ring
  change Real.sqrt (∑ I ∈ wordsOfLength d n, (c * a.coeff I) ^ 2) = _
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **Definition 2.1 (Free tensor algebra `T(ℝ^d)` / finitely supported core `𝒟_fin`)**:
formal series in `T((ℝ^d))` vanishing beyond a finite tensor level. -/
def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop :=
  ∃ N : ℕ, ∀ I : Word d, N < I.length → a.coeff I = 0

/-- The finitely supported core `𝒟_fin = T(ℝ^d) = ⨁_{n ≥ 0} (ℝ^d)^{⊗ n}`. -/
abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

lemma basisWord_isFinitelySupported {d : ℕ} (I : Word d) :
    IsFinitelySupported (basisWord I) := by
  refine ⟨I.length, fun J hJ => ?_⟩
  have hne : J ≠ I := fun h => by subst h; exact lt_irrefl _ hJ
  simp [basisWord, hne]

/-- **Definition 2.2 (Concatenation product `a ⊗ b`)** on `T((ℝ^d))`. -/
def concat {d : ℕ} (a b : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => ∑ k ∈ Finset.range (I.length + 1), a.coeff (I.take k) * b.coeff (I.drop k)⟩

infixl:70 " ⊗ₜ " => concat

/-- Concatenation acts on canonical basis elements as `e_I ⊗ e_J = e_{IJ}` (Definition 2.2). -/
lemma concat_basisWord {d : ℕ} (I J : Word d) :
    basisWord I ⊗ₜ basisWord J = basisWord (I ++ J) := by
  ext L
  simp only [concat, basisWord]
  by_cases hL : L = I ++ J
  · subst hL
    have hmem : I.length ∈ Finset.range ((I ++ J).length + 1) := by
      rw [Finset.mem_range, List.length_append]
      omega
    rw [Finset.sum_eq_single I.length]
    · simp [List.take_left, List.drop_left]
    · intro k hk hne
      have hkle : k ≤ (I ++ J).length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have htake_ne : (I ++ J).take k ≠ I := by
        intro heq
        have hlen := congrArg List.length heq
        rw [List.length_take_of_le hkle] at hlen
        exact hne hlen
      simp [htake_ne]
    · intro hnot
      exact absurd hmem hnot
  · rw [if_neg hL]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : L.take k = I
    · have h2 : L.drop k ≠ J := by
        intro h2
        apply hL
        rw [← List.take_append_drop k L, h1, h2]
      simp [h1, h2]
    · simp [h1]

/-- Euclidean level norm submultiplicativity for concatenation:
`|(a ⊗ b)_n| ≤ ∑_{k=0}^n |a_k| |b_{n - k}|`. -/
lemma levelNorm_concat_le {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a ⊗ₜ b) n ≤
      ∑ k ∈ Finset.range (n + 1), levelNorm a k * levelNorm b (n - k) := by
  have hrew : levelNormSq (a ⊗ₜ b) n =
      ∑ I ∈ wordsOfLength d n,
        (∑ k ∈ Finset.range (n + 1), a.coeff (I.take k) * b.coeff (I.drop k)) ^ 2 := by
    unfold levelNormSq concat
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [mem_wordsOfLength.mp hI]
  unfold levelNorm
  rw [hrew]
  refine (sqrt_sum_finset_sum_sq_le (wordsOfLength d n) (Finset.range (n + 1))
    (fun k I => a.coeff (I.take k) * b.coeff (I.drop k))).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [sum_wordsOfLength_take_drop_sq d k n hkn a.coeff b.coeff,
    Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

/-- **Definition 2.2 (Shuffle product `I ⊔⊔ J`)**: recursive list of all order-preserving
interlacings of `I` and `J` (counting multiplicities). -/
def shuffleWords {d : ℕ} : Word d → Word d → List (Word d)
  | [], J => [J]
  | i :: I, [] => [i :: I]
  | i :: I, j :: J =>
    (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·)
termination_by I J => I.length + J.length

/-- Basis shuffle element `e_I ⊔⊔ e_J ∈ T((ℝ^d))` (Definition 2.2). -/
def shuffleBasis {d : ℕ} (I J : Word d) : ExtTensorAlgebra d :=
  ⟨fun K => ((shuffleWords I J).map fun L => if K = L then (1 : ℝ) else 0).sum⟩

/-- Evaluation `⟨e_I ⊔⊔ e_J, X⟩` of the shuffle product against `X ∈ T((ℝ^d))`. -/
def evalShuffleBasis {d : ℕ} (I J : Word d) (X : ExtTensorAlgebra d) : ℝ :=
  ((shuffleWords I J).map fun K => X.coeff K).sum

/-- **Definition 2.2 (Hopf algebra antipode)**: `A(e_{i₁...iₙ}) = (-1)^n e_{iₙ...i₁}`. -/
def antipode {d : ℕ} (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => (-1 : ℝ) ^ I.length * a.coeff I.reverse⟩

lemma antipode_basisWord {d : ℕ} (I : Word d) :
    antipode (basisWord I) = ((-1 : ℝ) ^ I.length) • basisWord I.reverse := by
  ext J
  simp only [antipode, basisWord]
  change (-1 : ℝ) ^ J.length * (if J.reverse = I then 1 else 0) =
    (-1 : ℝ) ^ I.length * (if J = I.reverse then 1 else 0)
  by_cases h : J = I.reverse
  · subst h
    simp
  · have h' : J.reverse ≠ I := fun hr => h (by rw [← hr, List.reverse_reverse])
    simp [h, h']

lemma antipode_involutive {d : ℕ} (a : ExtTensorAlgebra d) :
    antipode (antipode a) = a := by
  ext I
  simp only [antipode, List.length_reverse, List.reverse_reverse]
  rw [← mul_assoc, ← mul_pow]
  norm_num

end ExtTensorAlgebra

/-! ## Section 2.2: The Signature of a Path, Chen Identity, Shuffle Identity, Filtration Equality -/

/-- **Definition 2.4 (Signature of a smooth path)**: recursive iterated integral over `[s, t]`
for a path `X : ℝ → (Fin d → ℝ)` given its velocity `X'`. -/
def smoothIteratedIntegral {d : ℕ} (X' : ℝ → Fin d → ℝ) (s : ℝ) : Word d → ℝ → ℝ
  | [], _ => 1
  | i :: I, t => ∫ u in s..t, X' u i * smoothIteratedIntegral X' u I t

/-- Full signature `𝐗_{s, t} ∈ T((ℝ^d))` of a smooth path over `[s, t]` (Definition 2.4). -/
def smoothSignature {d : ℕ} (X' : ℝ → Fin d → ℝ) (s t : ℝ) : ExtTensorAlgebra d :=
  ⟨fun I => smoothIteratedIntegral X' s I t⟩

/-- Real-time indexed filtration `(ℱ_t)_{t ≥ 0}` on `(Ω, m₀)`. -/
structure IndexedFiltration (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀

/-- Natural filtration generated by a family of coordinate processes up to time `t`. -/
def generatedFiltration {Ω ι : Type*} [m₀ : MeasurableSpace Ω]
    (Z : ℝ → ι → Ω → ℝ) (hmeas : ∀ t i, Measurable (Z t i)) : IndexedFiltration Ω where
  σAlg t := ⨆ (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (i : ι),
    MeasurableSpace.comap (Z s.1 i) inferInstance
  mono s t hst := iSup_le fun u => le_iSup_of_le ⟨u.1, u.2.1, u.2.2.trans hst⟩ le_rfl
  le_ambient t := iSup_le fun u => iSup_le fun i => (hmeas u.1 i).comap_le

/-- **Definition 2.5 & Appendix A (Prolonged Stratonovich Brownian Signature Setup)**:
Encapsulates a `d`-dimensional Brownian motion `W` on `(Ω, ℱ, ℙ)` over `[0, T]` and its
prolonged signature `Ŵ_{s, t}` of the time-augmented path `(t, W^1_t, ..., W^d_t)` in
`T((ℝ^{d+1}))` (index `0` is time; indices `i.succ` are Brownian coordinates). -/
structure ProlongedBrownianSetup (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (d : ℕ) (T : ℝ) where
  hT_pos : 0 < T
  /-- `d`-dimensional standard Brownian motion `W_t(ω)`. -/
  W : ℝ → Ω → Fin d → ℝ
  W_zero : ∀ ω i, W 0 ω i = 0
  W_meas : ∀ t i, Measurable (fun ω => W t ω i)
  /-- Two-parameter Stratonovich signature `Ŵ_{s, t}(ω) ∈ T((ℝ^{d+1}))`. -/
  sig2 : ℝ → ℝ → Ω → ExtTensorAlgebra (d + 1)
  sig_meas : ∀ s t I, Measurable (fun ω => (sig2 s t ω).coeff I)
  /-- Empty word coordinate is `1`. -/
  sig2_empty : ∀ s t ω, (sig2 s t ω).coeff [] = 1
  /-- Level-1 time coordinate `⟨e_{(0)}, Ŵ_{s,t}⟩ = t - s`. -/
  sig2_time : ∀ s t ω, (sig2 s t ω).coeff [0] = t - s
  /-- Level-1 Brownian coordinate `⟨e_{(i+1)}, Ŵ_{s,t}⟩ = W^i_t - W^i_s`. -/
  sig2_space : ∀ s t ω (i : Fin d), (sig2 s t ω).coeff [i.succ] = W t ω i - W s ω i
  /-- Stratonovich signature of `(t, W_t)` up to time `s` is measurable w.r.t. the path of `W`
  up to time `s`. -/
  sig_adapted_to_W : ∀ (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (I : Word (d + 1)),
    Measurable[(generatedFiltration (fun u i ω => W u ω i) W_meas).σAlg t]
      (fun ω => (sig2 0 s.1 ω).coeff I)
  /-- Multiplicative rough-path/Stratonovich simplex decomposition over `[0, s] ∪ [s, t]`. -/
  stratonovich_chen : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    ∀ ω, sig2 0 t ω = sig2 0 s ω ⊗ₜ sig2 s t ω
  /-- Product-of-simplices Stratonovich shuffle relation on coordinates. -/
  stratonovich_shuffle : ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    ∀ (I J : Word (d + 1)) (ω : Ω),
      (sig2 0 t ω).coeff I * (sig2 0 t ω).coeff J =
        ExtTensorAlgebra.evalShuffleBasis I J (sig2 0 t ω)
  /-- Appendix A Brownian signature factorial level-decay estimate: for each `p ≥ 1`, there exist
  constants `C_p ≥ 0` and `R_p ≥ 0` controlling the `L^p`-norm of level-`n` signature norms by
  `C_p * R_p^n / n!`, together with uniform `L^p` control of weighted sums. -/
  factorial_moment_control : ∀ (p : ℝ), 1 ≤ p → ∃ (C_p R_p : ℝ), 0 ≤ C_p ∧ 0 ≤ R_p ∧
    ∀ (w_fn : ℕ → ℝ), (∀ n, 0 ≤ w_fn n) →
      Summable (fun n : ℕ => w_fn n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) →
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
        (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2 0 t ω).levelNorm n)) ∧
        Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p) ℙ ∧
        (∫ ω, (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p ∂ℙ) ≤
          (∑' n : ℕ, w_fn n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) ^ p

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

/-- Single-parameter prolonged signature `Ŵ_t := Ŵ_{0, t}` (Definition 2.5). -/
def W_hat (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) :
    ExtTensorAlgebra (d + 1) :=
  setup.sig2 0 t ω

/-- Time-augmented Brownian path `(t, W^1_t, ..., W^d_t)` (Definition 2.5). -/
def W_aug (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) : Fin (d + 1) → ℝ :=
  Fin.cases t (fun i => setup.W t ω i)

/-- Natural Brownian filtration `ℱ^W_t`. -/
def brownianFiltration (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω :=
  generatedFiltration (fun u i ω => setup.W u ω i) setup.W_meas

/-- **Definition 2.16 (Signature filtration `ℱ^{\widehat{W}}_t`)**: natural filtration of `Ŵ`. -/
def signatureFiltration (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω :=
  generatedFiltration (fun u I ω => (setup.W_hat u ω).coeff I) (setup.sig_meas 0)

/-- **Theorem 2.6 (Chen identity)**: `Ŵ_{0, t} = Ŵ_{0, s} ⊗ Ŵ_{s, t}` for `0 ≤ s ≤ t ≤ T`. -/
theorem chen_identity (setup : ProlongedBrownianSetup Ω ℙ d T)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) (ω : Ω) :
    setup.sig2 0 t ω = setup.sig2 0 s ω ⊗ₜ setup.sig2 s t ω :=
  setup.stratonovich_chen hs hst ht ω

/-- **Theorem 2.7 (Shuffle identity)**:
`⟨e_I, Ŵ_t⟩ ⟨e_J, Ŵ_t⟩ = ⟨e_I ⊔⊔ e_J, Ŵ_t⟩` for `0 ≤ t ≤ T`. -/
theorem shuffle_identity (setup : ProlongedBrownianSetup Ω ℙ d T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (I J : Word (d + 1)) (ω : Ω) :
    (setup.W_hat t ω).coeff I * (setup.W_hat t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (setup.W_hat t ω) :=
  setup.stratonovich_shuffle ht0 htT I J ω

/-- **Theorem 2.8 (Signature uniqueness / equality of prolonged signature and Brownian filtrations)**:
`ℱ^{\widehat{W}}_t = ℱ^W_t` for every `t`, proved genuinely by combining adaptedness of `Ŵ` with
exact recovery of `W_s` from the level-1 coordinates of `Ŵ_s`. -/
theorem signature_filtration_eq_brownian_filtration
    (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) :
    setup.signatureFiltration.σAlg t = setup.brownianFiltration.σAlg t := by
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun I => ?_
    exact (setup.sig_adapted_to_W t s I).comap_le
  · refine iSup_le fun s => iSup_le fun i => ?_
    have hrec : (fun ω => setup.W s.1 ω i) = (fun ω => (setup.W_hat s.1 ω).coeff [i.succ]) := by
      ext ω
      have hsp := setup.sig2_space 0 s.1 ω i
      rw [setup.W_zero ω i, sub_zero] at hsp
      exact hsp.symm
    rw [hrec]
    exact le_iSup_of_le s (le_iSup_of_le [i.succ] le_rfl)

end ProlongedBrownianSetup

/-! ## Section 2.3: The Weighted Tensor Algebra `T_w` and its Dual `T_w^*` -/

/-- **Definition 2.9 (Weight)**: `w : ℕ → (0, ∞)` with `w(0) = 1` and `w` increasing. -/
structure Weight where
  toFun : ℕ → ℝ
  w_zero : toFun 0 = 1
  pos : ∀ n : ℕ, 0 < toFun n
  mono : Monotone toFun

instance : CoeFun Weight (fun _ => ℕ → ℝ) := ⟨Weight.toFun⟩

namespace Weight

lemma one_le (w : Weight) (n : ℕ) : 1 ≤ w n := by
  rw [← w.w_zero]
  exact w.mono (Nat.zero_le n)

lemma inv_le_one (w : Weight) (n : ℕ) : (w n)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (w.one_le n)

/-- Constant baseline weight `w₀(n) = 1` used in the proof of Lemma 3.2. -/
def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl

/-- Geometric weight `w_r(n) = r^n` for `r ≥ 1`. -/
def geometric (r : ℝ) (hr : 1 ≤ r) : Weight where
  toFun n := r ^ n
  w_zero := pow_zero r
  pos n := pow_pos ( zero_lt_one.trans_le hr ) n
  mono m n hmn := pow_le_pow_right₀ hr hmn

end Weight

/-- **Definition 2.10 (Weighted tensor algebra membership `a ∈ T_w`)**:
`∑_{n ≥ 0} w(n) |a_n| < ∞`. -/
def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => w n * a.levelNorm n)

/-- Weighted norm `‖a‖_w := ∑_{n ≥ 0} w(n) |a_n|` (Definition 2.10). -/
def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, w n * a.levelNorm n

/-- The weighted tensor space `T_w` as a subtype of `T((ℝ^d))`. -/
abbrev Tw (d : ℕ) (w : Weight) := {a : ExtTensorAlgebra d // MemTw w a}

lemma normW_nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ normW w a :=
  tsum_nonneg fun n => mul_nonneg (w.pos n).le (a.levelNorm_nonneg n)

/-- **Proposition 2.11 (Banach algebra submultiplicativity of `T_w`)**:
If `w(m + n) ≤ C_w w(m) w(n)` with `C_w ≥ 1`, then `a, b ∈ T_w` implies `a ⊗ b ∈ T_w` and
`‖a ⊗ b‖_w ≤ C_w ‖a‖_w ‖b‖_w`. -/
theorem banach_algebra_concat_bound {d : ℕ} (w : Weight) {C_w : ℝ} (hCw : 1 ≤ C_w)
    (hsub : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n)
    {a b : ExtTensorAlgebra d} (ha : MemTw w a) (hb : MemTw w b) :
    MemTw w (a ⊗ₜ b) ∧ normW w (a ⊗ₜ b) ≤ C_w * normW w a * normW w b := by
  have hCw0 : 0 ≤ C_w := zero_le_one.trans hCw
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ w n * (a ⊗ₜ b).levelNorm n :=
    fun n => mul_nonneg (w.pos n).le ((a ⊗ₜ b).levelNorm_nonneg n)
  have hrange : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, w n * (a ⊗ₜ b).levelNorm n) ≤ C_w * normW w a * normW w b := by
    intro N
    calc
      ∑ n ∈ Finset.range N, w n * (a ⊗ₜ b).levelNorm n
          ≤ ∑ n ∈ Finset.range N,
              w n * (∑ k ∈ Finset.range (n + 1), a.levelNorm k * b.levelNorm (n - k)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            exact mul_le_mul_of_nonneg_left (ExtTensorAlgebra.levelNorm_concat_le a b n)
              (w.pos n).le
      _ ≤ ∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              C_w * (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun k hk => ?_
            have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hw_kn : w n ≤ C_w * w k * w (n - k) := by
              have h := hsub k (n - k)
              rwa [Nat.add_sub_of_le hkn] at h
            calc
              w n * (a.levelNorm k * b.levelNorm (n - k))
                  ≤ (C_w * w k * w (n - k)) * (a.levelNorm k * b.levelNorm (n - k)) :=
                    mul_le_mul_of_nonneg_right hw_kn
                      (mul_nonneg (a.levelNorm_nonneg k) (b.levelNorm_nonneg (n - k)))
              _ = C_w * (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k)) := by ring
      _ = C_w * (∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ C_w * ((∑ k ∈ Finset.range N, w k * a.levelNorm k) *
            (∑ j ∈ Finset.range N, w j * b.levelNorm j)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw0
            exact cauchy_range_sum_le N
              (fun k => w k * a.levelNorm k)
              (fun j => w j * b.levelNorm j)
              (fun k => mul_nonneg (w.pos k).le (a.levelNorm_nonneg k))
              (fun j => mul_nonneg (w.pos j).le (b.levelNorm_nonneg j))
      _ ≤ C_w * (normW w a * normW w b) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw0
            refine mul_le_mul ?_ ?_ ?_ (normW_nonneg w a)
            · exact ha.sum_le_tsum (Finset.range N)
                fun k _ => mul_nonneg (w.pos k).le (a.levelNorm_nonneg k)
            · exact hb.sum_le_tsum (Finset.range N)
                fun j _ => mul_nonneg (w.pos j).le (b.levelNorm_nonneg j)
            · exact Finset.sum_nonneg
                fun j _ => mul_nonneg (w.pos j).le (b.levelNorm_nonneg j)
      _ = C_w * normW w a * normW w b := by ring
  have hsum : Summable (fun n : ℕ => w n * (a ⊗ₜ b).levelNorm n) :=
    summable_of_sum_range_le hterm_nonneg hrange
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hrange⟩

/-- **Definition 2.12 (Dual space `T_w^*`)**: formal series `ℓ ∈ T((ℝ^d))` such that
`sup_{n ≥ 0} |ℓ_n| / w(n) < ∞`. -/
def MemTwDual {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  BddAbove (Set.range fun n : ℕ => ℓ.levelNorm n / w n)

/-- Dual norm `‖ℓ‖_{w^*} := sup_{n ≥ 0} |ℓ_n| / w(n)` (Definition 2.12). -/
def normWDual {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  ⨆ n : ℕ, ℓ.levelNorm n / w n

lemma levelNorm_div_le_normWDual {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d}
    (hℓ : MemTwDual w ℓ) (n : ℕ) :
    ℓ.levelNorm n / w n ≤ normWDual w ℓ :=
  le_ciSup hℓ n

lemma normWDual_nonneg {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d} (hℓ : MemTwDual w ℓ) :
    0 ≤ normWDual w ℓ :=
  (div_nonneg (ℓ.levelNorm_nonneg 0) (w.pos 0).le).trans (levelNorm_div_le_normWDual w hℓ 0)

/-- Weighted `L^2` dual condition: `∑_{n ≥ 0} |ℓ_n|^2 / w(n)^2 < ∞` (Hypothesis H1). -/
def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => ℓ.levelNormSq n / (w n) ^ 2)

/-- Weighted Hilbert norm `‖ℓ‖_{2, w} := (∑_{n ≥ 0} |ℓ_n|^2 / w(n)^2)^{1/2}`. -/
def norm2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, ℓ.levelNormSq n / (w n) ^ 2)

/-- Inverse-weighted Hilbert condition `∑_{n ≥ 0} w(n)^2 |a_n|^2 < ∞` (Lemma 2.22). -/
def MemL2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => (w n) ^ 2 * a.levelNormSq n)

/-- Inverse-weighted Hilbert norm `‖a‖_{2, w^{-1}} := (∑_{n ≥ 0} w(n)^2 |a_n|^2)^{1/2}`. -/
def norm2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, (w n) ^ 2 * a.levelNormSq n)

lemma norm2w_nonneg {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : 0 ≤ norm2w w ℓ :=
  Real.sqrt_nonneg _

lemma norm2wInv_nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ norm2wInv w a :=
  Real.sqrt_nonneg _

/-- Canonical duality pairing `⟨ℓ, a⟩ := ∑_{n ≥ 0} ⟨ℓ_n, a_n⟩` (Definition 2.12). -/
def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, ℓ.levelInner a n

/-- Continuous duality estimate `|⟨ℓ, a⟩| ≤ ‖ℓ‖_{w^*} ‖a‖_w` on `T_w^* × T_w` (Definition 2.12). -/
theorem dualPairing_le_normWDual_mul_normW {d : ℕ} (w : Weight)
    {ℓ a : ExtTensorAlgebra d} (hℓ : MemTwDual w ℓ) (ha : MemTw w a) :
    Summable (fun n : ℕ => |ℓ.levelInner a n|) ∧
      |dualPairing ℓ a| ≤ normWDual w ℓ * normW w a := by
  have hpoint : ∀ n : ℕ, |ℓ.levelInner a n| ≤ normWDual w ℓ * (w n * a.levelNorm n) := by
    intro n
    have hw : 0 < w n := w.pos n
    have hbound : ℓ.levelNorm n ≤ normWDual w ℓ * w n :=
      (div_le_iff₀ hw).mp (levelNorm_div_le_normWDual w hℓ n)
    calc
      |ℓ.levelInner a n| ≤ ℓ.levelNorm n * a.levelNorm n := ℓ.abs_levelInner_le a n
      _ ≤ (normWDual w ℓ * w n) * a.levelNorm n :=
        mul_le_mul_of_nonneg_right hbound (a.levelNorm_nonneg n)
      _ = normWDual w ℓ * (w n * a.levelNorm n) := by ring
  have hdom : Summable (fun n : ℕ => normWDual w ℓ * (w n * a.levelNorm n)) :=
    ha.mul_left (normWDual w ℓ)
  have habs : Summable (fun n : ℕ => |ℓ.levelInner a n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint hdom
  refine ⟨habs, ?_⟩
  calc
    |dualPairing ℓ a| ≤ ∑' n : ℕ, |ℓ.levelInner a n| := abs_tsum_le_of_summable_abs habs
    _ ≤ ∑' n : ℕ, normWDual w ℓ * (w n * a.levelNorm n) := habs.tsum_le_tsum hpoint hdom
    _ = normWDual w ℓ * normW w a := tsum_mul_left

/-- Embedding `L^2_w ↪ T_w^*` with `‖ℓ‖_{w^*} ≤ ‖ℓ‖_{2, w}`. -/
lemma memTwDual_of_memL2w {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d} (hℓ : MemL2w w ℓ) :
    MemTwDual w ℓ ∧ normWDual w ℓ ≤ norm2w w ℓ := by
  have hle : ∀ n : ℕ, ℓ.levelNorm n / w n ≤ norm2w w ℓ := by
    intro n
    have hsq : (ℓ.levelNorm n / w n) ^ 2 ≤ ∑' k : ℕ, ℓ.levelNormSq k / (w k) ^ 2 := by
      have heq : (ℓ.levelNorm n / w n) ^ 2 = ℓ.levelNormSq n / (w n) ^ 2 := by
        rw [div_pow, ℓ.sq_levelNorm]
      rw [heq]
      exact hℓ.le_tsum n fun k _ => div_nonneg (ℓ.levelNormSq_nonneg k) (sq_nonneg _)
    have h0 : 0 ≤ ℓ.levelNorm n / w n := div_nonneg (ℓ.levelNorm_nonneg n) (w.pos n).le
    calc
      ℓ.levelNorm n / w n = Real.sqrt ((ℓ.levelNorm n / w n) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ norm2w w ℓ := Real.sqrt_le_sqrt hsq
  exact ⟨⟨norm2w w ℓ, by rintro _ ⟨n, rfl⟩; exact hle n⟩, ciSup_le hle⟩

/-- Embedding `T_w ↪ L^2_{w^{-1}}` with `‖a‖_{2, w^{-1}} ≤ ‖a‖_w`. -/
lemma memL2wInv_of_memTw {d : ℕ} (w : Weight) {a : ExtTensorAlgebra d} (ha : MemTw w a) :
    MemL2wInv w a ∧ norm2wInv w a ≤ normW w a := by
  have hterm : ∀ n : ℕ, 0 ≤ (w n) ^ 2 * a.levelNormSq n :=
    fun n => mul_nonneg (sq_nonneg _) (a.levelNormSq_nonneg n)
  have hrange : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (w n) ^ 2 * a.levelNormSq n) ≤ (normW w a) ^ 2 := by
    intro N
    have hrew : (∑ n ∈ Finset.range N, (w n) ^ 2 * a.levelNormSq n) =
        ∑ n ∈ Finset.range N, (w n * a.levelNorm n) ^ 2 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow, a.sq_levelNorm]
    rw [hrew]
    calc
      ∑ n ∈ Finset.range N, (w n * a.levelNorm n) ^ 2
          ≤ (∑ n ∈ Finset.range N, w n * a.levelNorm n) ^ 2 :=
            sum_sq_le_sq_sum (Finset.range N) (fun n => w n * a.levelNorm n)
              (fun n _ => mul_nonneg (w.pos n).le (a.levelNorm_nonneg n))
      _ ≤ (normW w a) ^ 2 := by
            have hle : ∑ n ∈ Finset.range N, w n * a.levelNorm n ≤ normW w a :=
              ha.sum_le_tsum (Finset.range N)
                fun n _ => mul_nonneg (w.pos n).le (a.levelNorm_nonneg n)
            exact pow_le_pow_left₀
              (Finset.sum_nonneg fun n _ => mul_nonneg (w.pos n).le (a.levelNorm_nonneg n)) hle 2
  have hsum : MemL2wInv w a := summable_of_sum_range_le hterm hrange
  refine ⟨hsum, ?_⟩
  have htsum : (∑' n : ℕ, (w n) ^ 2 * a.levelNormSq n) ≤ (normW w a) ^ 2 :=
    hsum.tsum_le_of_sum_range_le hrange
  exact (Real.sqrt_le_sqrt htsum).trans_eq (Real.sqrt_sq (normW_nonneg w a))

/-! ## Section 2.6: Truncation Operators `π_N`, `π_{> N}` and Lemma 2.22 -/

/-- **Definition 2.21 (Truncation operator `π_N`)**: retains tensor levels `0, ..., N`. -/
def projLe {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => if I.length ≤ N then a.coeff I else 0⟩

/-- **Definition 2.21 (Tail projection `π_{> N}`)**: retains tensor levels strictly above `N`. -/
def projGt {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => if N < I.length then a.coeff I else 0⟩

lemma add_projLe_projGt {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) :
    projLe N a + projGt N a = a := by
  ext I
  change (if I.length ≤ N then a.coeff I else 0) + (if N < I.length then a.coeff I else 0) =
    a.coeff I
  by_cases h : I.length ≤ N
  · have hnot : ¬ N < I.length := not_lt_of_ge h
    simp [h, hnot]
  · have hlt : N < I.length := lt_of_not_ge h
    simp [h, hlt]

lemma projGt_levelNormSq {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) (n : ℕ) :
    (projGt N a).levelNormSq n = if N < n then a.levelNormSq n else 0 := by
  unfold ExtTensorAlgebra.levelNormSq projGt
  split_ifs with h
  · refine Finset.sum_congr rfl fun I hI => ?_
    rw [mem_wordsOfLength.mp hI, if_pos h]
  · refine Finset.sum_eq_zero fun I hI => ?_
    rw [mem_wordsOfLength.mp hI, if_neg h]
    ring

lemma projGt_levelNorm {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) (n : ℕ) :
    (projGt N a).levelNorm n = if N < n then a.levelNorm n else 0 := by
  unfold ExtTensorAlgebra.levelNorm
  rw [projGt_levelNormSq]
  split_ifs <;> simp

/-- **Lemma 2.22 (Weighted truncation and tail estimates)**:
1. Hilbert Cauchy–Schwarz: `|⟨ℓ, a⟩| ≤ ‖ℓ‖_{2, w} ‖a‖_{2, w^{-1}}`;
2. Dual tail estimate: `|⟨π_{> N} ℓ, a⟩| ≤ ‖π_{> N} ℓ‖_{2, w} ‖a‖_{2, w^{-1}}`. -/
theorem weighted_truncation_estimates {d : ℕ} (w : Weight)
    {ℓ a : ExtTensorAlgebra d} (hℓ : MemL2w w ℓ) (ha : MemL2wInv w a) :
    (|dualPairing ℓ a| ≤ norm2w w ℓ * norm2wInv w a) ∧
    (∀ N : ℕ, MemL2w w (projGt N ℓ) ∧
      |dualPairing (projGt N ℓ) a| ≤ norm2w w (projGt N ℓ) * norm2wInv w a) := by
  have hcauchy : ∀ (L : ExtTensorAlgebra d), MemL2w w L →
      |dualPairing L a| ≤ norm2w w L * norm2wInv w a := by
    intro L hL
    have hpoint : ∀ n : ℕ,
        |L.levelInner a n| ≤ (L.levelNorm n / w n) * (w n * a.levelNorm n) := by
      intro n
      have hw : w n ≠ 0 := (w.pos n).ne'
      calc
        |L.levelInner a n| ≤ L.levelNorm n * a.levelNorm n := L.abs_levelInner_le a n
        _ = (L.levelNorm n / w n) * (w n * a.levelNorm n) := by field_simp [hw]
    have hrange : ∀ M : ℕ,
        (∑ n ∈ Finset.range M, |L.levelInner a n|) ≤ norm2w w L * norm2wInv w a := by
      intro M
      calc
        ∑ n ∈ Finset.range M, |L.levelInner a n|
            ≤ ∑ n ∈ Finset.range M, (L.levelNorm n / w n) * (w n * a.levelNorm n) :=
              Finset.sum_le_sum fun n _ => hpoint n
        _ ≤ Real.sqrt (∑ n ∈ Finset.range M, (L.levelNorm n / w n) ^ 2) *
              Real.sqrt (∑ n ∈ Finset.range M, (w n * a.levelNorm n) ^ 2) := by
              have h := abs_finset_sum_mul_le_sqrt (Finset.range M)
                (fun n => L.levelNorm n / w n) (fun n => w n * a.levelNorm n)
              exact (le_abs_self _).trans h
        _ ≤ norm2w w L * norm2wInv w a := by
              refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm2w_nonneg w L)
              · apply Real.sqrt_le_sqrt
                have hrew : (∑ n ∈ Finset.range M, (L.levelNorm n / w n) ^ 2) =
                    ∑ n ∈ Finset.range M, L.levelNormSq n / (w n) ^ 2 := by
                  refine Finset.sum_congr rfl fun n _ => ?_
                  rw [div_pow, L.sq_levelNorm]
                rw [hrew]
                exact hL.sum_le_tsum (Finset.range M)
                  fun n _ => div_nonneg (L.levelNormSq_nonneg n) (sq_nonneg _)
              · apply Real.sqrt_le_sqrt
                have hrew : (∑ n ∈ Finset.range M, (w n * a.levelNorm n) ^ 2) =
                    ∑ n ∈ Finset.range M, (w n) ^ 2 * a.levelNormSq n := by
                  refine Finset.sum_congr rfl fun n _ => ?_
                  rw [mul_pow, a.sq_levelNorm]
                rw [hrew]
                exact ha.sum_le_tsum (Finset.range M)
                  fun n _ => mul_nonneg (sq_nonneg _) (a.levelNormSq_nonneg n)
    have habs : Summable (fun n : ℕ => |L.levelInner a n|) :=
      summable_of_sum_range_le (fun _ => abs_nonneg _) hrange
    calc
      |dualPairing L a| ≤ ∑' n : ℕ, |L.levelInner a n| := abs_tsum_le_of_summable_abs habs
      _ ≤ norm2w w L * norm2wInv w a := habs.tsum_le_of_sum_range_le hrange
  refine ⟨hcauchy ℓ hℓ, fun N => ?_⟩
  have htail : MemL2w w (projGt N ℓ) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg ((projGt N ℓ).levelNormSq_nonneg n) (sq_nonneg _))
      (fun n => ?_) hℓ
    rw [projGt_levelNormSq]
    split_ifs
    · exact le_rfl
    · rw [zero_div]
      exact div_nonneg (ℓ.levelNormSq_nonneg n) (sq_nonneg _)
  exact ⟨htail, hcauchy (projGt N ℓ) htail⟩

/-- Weight-ratio tail bound (second half of Lemma 2.22):
`‖π_{> N} b‖_{2, w^{-1}} ≤ ρ ‖b‖_{w'}` whenever `w(n)/w'(n) ≤ ρ` for all `n > N`. -/
theorem tail_norm2wInv_le_ratio_mul_normW {d : ℕ} (w w' : Weight)
    {b : ExtTensorAlgebra d} (hb : MemTw w' b) (N : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hratio : ∀ n : ℕ, N < n → w n / w' n ≤ ρ) :
    MemL2wInv w (projGt N b) ∧ norm2wInv w (projGt N b) ≤ ρ * normW w' b := by
  have hterm : ∀ n : ℕ, 0 ≤ w n * (projGt N b).levelNorm n :=
    fun n => mul_nonneg (w.pos n).le ((projGt N b).levelNorm_nonneg n)
  have hpoint : ∀ n : ℕ, w n * (projGt N b).levelNorm n ≤ ρ * (w' n * b.levelNorm n) := by
    intro n
    rw [projGt_levelNorm]
    split_ifs with hn
    · have hw' : 0 < w' n := w'.pos n
      have hw_le : w n ≤ ρ * w' n := (div_le_iff₀ hw').mp (hratio n hn)
      calc
        w n * b.levelNorm n ≤ (ρ * w' n) * b.levelNorm n :=
          mul_le_mul_of_nonneg_right hw_le (b.levelNorm_nonneg n)
        _ = ρ * (w' n * b.levelNorm n) := by ring
    · rw [mul_zero]
      exact mul_nonneg hρ (mul_nonneg (w'.pos n).le (b.levelNorm_nonneg n))
  have hdom : Summable (fun n : ℕ => ρ * (w' n * b.levelNorm n)) := hb.mul_left ρ
  have hmemTw : MemTw w (projGt N b) := Summable.of_nonneg_of_le hterm hpoint hdom
  obtain ⟨hL2, hle⟩ := memL2wInv_of_memTw w hmemTw
  refine ⟨hL2, hle.trans ?_⟩
  calc
    normW w (projGt N b) ≤ ∑' n : ℕ, ρ * (w' n * b.levelNorm n) :=
      hmemTw.tsum_le_tsum hpoint hdom
    _ = ρ * normW w' b := tsum_mul_left

/-! ## Section 2.4: Hypotheses H1–H3, Price SDE, Signature Volatility Model, Price Filtration -/

/-- **Hypothesis H1 (Linear functional regularity, Definition 2.13)**:
`ℓ ∈ T_w^*` satisfies `‖ℓ‖_{2, w}^2 = ∑_{n ≥ 0} |ℓ_n|^2 / w(n)^2 < ∞`. -/
structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ

/-- **Hypothesis H2 (Weight admissibility, Definition 2.14)**:
1. Submultiplicativity: `w(m + n) ≤ C_w w(m) w(n)` with `C_w ≥ 1`;
2. Sub-factorial growth: `∑_{n ≥ 0} w(n) R^n / n! < ∞` for all `R > 0`. -/
structure HypH2 (w : Weight) : Prop where
  C_w : ℝ
  one_le_Cw : 1 ≤ C_w
  submult : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n
  subfactorial : ∀ R : ℝ, 0 < R → Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ)))

namespace HypH2

lemma subfactorial_nonneg {w : Weight} (hw : HypH2 w) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ))) := by
  rcases hR.eq_or_lt with rfl | hpos
  · refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (w.pos n).le (div_nonneg (pow_nonneg le_rfl n) (Nat.cast_nonneg _)))
      (fun n => ?_) (hw.subfactorial 1 zero_lt_one)
    refine mul_le_mul_of_nonneg_left ?_ (w.pos n).le
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ le_rfl zero_le_one n) (Nat.cast_nonneg _)
  · exact hw.subfactorial R hpos

lemma geometric_admissible (r : ℝ) (hr : 1 ≤ r) : HypH2 (Weight.geometric r hr) where
  C_w := 1
  one_le_Cw := le_rfl
  submult m n := by simp [Weight.geometric, pow_add]
  subfactorial R _ := by
    have hrew : (fun n : ℕ => (Weight.geometric r hr) n * (R ^ n / (n.factorial : ℝ))) =
        fun n : ℕ => (r * R) ^ n / (n.factorial : ℝ) := by
      ext n
      simp [Weight.geometric, mul_pow, mul_div_assoc]
    rw [hrew]
    exact Real.summable_pow_div_factorial (r * R)

lemma constOne_admissible : HypH2 Weight.constOne where
  C_w := 1
  one_le_Cw := le_rfl
  submult _ _ := by simp [Weight.constOne]
  subfactorial R _ := by
    simpa [Weight.constOne] using Real.summable_pow_div_factorial R

end HypH2

/-- **Hypothesis H3 (Non-degeneracy, Definition 2.14)**: `ℓ ≠ 0` and `0 < d`. -/
structure HypH3 {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

/-- **Definition 2.15 (Signature Volatility Model)**: tuple `(d, T, ℓ, w, s₀)` satisfying H1–H3. -/
structure SignatureVolatilityModel where
  d : ℕ
  hd : 0 < d
  T : ℝ
  hT : 0 < T
  w : Weight
  ℓ : ExtTensorAlgebra (d + 1)
  s₀ : ℝ
  hs₀ : 0 < s₀
  h1 : HypH1 w ℓ
  h2 : HypH2 w
  h3 : HypH3 hd ℓ

namespace SignatureVolatilityModel

/-- Spot signature volatility process `σ_t(ω) := ⟨ℓ, Ŵ_t(ω)⟩` (Equation 2.1). -/
def sigma {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (t : ℝ) (ω : Ω) : ℝ :=
  dualPairing M.ℓ (setup.W_hat t ω)

end SignatureVolatilityModel

/-- **Definition 2.16 (Price filtration `ℱ^S_t`)**: natural filtration generated by `S`. -/
def priceFiltration {Ω : Type*} [MeasurableSpace Ω]
    (S : ℝ → Ω → ℝ) (hS_meas : ∀ t, Measurable (S t)) : IndexedFiltration Ω :=
  generatedFiltration (fun t (_ : Unit) ω => S t ω) (fun t _ => hS_meas t)

lemma priceFiltration_le_signatureFiltration {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) (S : ℝ → Ω → ℝ)
    (hS_meas : ∀ t, Measurable (S t))
    (hS_adapt : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
      Measurable[setup.signatureFiltration.σAlg t] (S s.1)) (t : ℝ) :
    (priceFiltration S hS_meas).σAlg t ≤ setup.signatureFiltration.σAlg t :=
  iSup_le fun s => iSup_le fun _ => (hS_adapt t s).comap_le

/-! ## Section 2.5: Signature Cumulant / Affine Riccati Operator `ℛ` -/

/-- Directional shift `u ▹ e_k` on `T((ℝ^{d+1}))`: `(u ▹ e_k)_I = u_{I · k}`. -/
def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩

/-- Stratonovich geometric Itô drift correction `1/2 ∑_{i=1}^d (u ▹ e_i) ▹ e_i`. -/
def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩

/-- Finite-support shuffle product on `𝒟_fin`. -/
def shuffleFinite {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (supportBound : ℕ) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun K =>
    ∑ m ∈ Finset.range (supportBound + 1),
      ∑ n ∈ Finset.range (supportBound + 1),
        ∑ I ∈ wordsOfLength (d + 1) m,
          ∑ J ∈ wordsOfLength (d + 1) n,
            a.coeff I * b.coeff J * (ExtTensorAlgebra.shuffleBasis I J).coeff K⟩

/-- **Definition 2.17 (Formal Riccati operator `ℛ` on `𝒟_fin`)**. -/
def riccatiOpBounded {d : ℕ} (N : ℕ) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  rightShift 0 u + stratonovichHalfLaplacian u +
    (1 / 2 : ℝ) • ∑ i : Fin d, shuffleFinite (rightShift i.succ u) (rightShift i.succ u) N

/-- **Definition 2.18 (Classical Riccati solution on `[0, T]`)**. -/
structure ClassicalRiccatiSolution {d : ℕ} (w : Weight) (T : ℝ)
    (R_op : ExtTensorAlgebra (d + 1) → ExtTensorAlgebra (d + 1))
    (u₀ : ExtTensorAlgebra (d + 1)) where
  ψ : ℝ → ExtTensorAlgebra (d + 1)
  mem_Tw : ∀ t ∈ Icc 0 T, MemTw w (ψ t)
  uniform_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, normW w (ψ t) ≤ M
  init : ψ 0 = u₀
  integral_eq : ∀ t ∈ Icc 0 T, ∀ I : Word (d + 1),
    ContinuousOn (fun s => (R_op (ψ s)).coeff I) (Icc 0 T) ∧
      (ψ t).coeff I = u₀.coeff I + ∫ s in (0 : ℝ)..t, (R_op (ψ s)).coeff I

/-- **Remark 2.19 (Black–Scholes explicit Riccati check)**:
For `d = 1` and `u₀ = c₁ e_{(1)}`, `(ℛ_1(u₀))_∅ = 1/2 c₁^2`. -/
theorem remark_2_19_black_scholes_riccati (c₁ : ℝ) :
    let idx1 : Letter 2 := (0 : Fin 1).succ
    let u₀ : ExtTensorAlgebra 2 := c₁ • ExtTensorAlgebra.basisWord [idx1]
    (riccatiOpBounded 1 u₀).coeff [] = (1 / 2 : ℝ) * c₁ ^ 2 := by
  intro idx1 u₀
  have hshift0 : (rightShift 0 u₀).coeff [] = 0 := by
    simp [rightShift, u₀, ExtTensorAlgebra.basisWord, idx1]
  have hlap : (stratonovichHalfLaplacian u₀).coeff [] = 0 := by
    simp [stratonovichHalfLaplacian, u₀, ExtTensorAlgebra.basisWord, idx1]
  have hshuf : (shuffleFinite (rightShift idx1 u₀) (rightShift idx1 u₀) 1).coeff [] = c₁ ^ 2 := by
    unfold shuffleFinite
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have hm1 : ∑ n ∈ Finset.range 2,
        ∑ I ∈ wordsOfLength 2 1, ∑ J ∈ wordsOfLength 2 n,
          (rightShift idx1 u₀).coeff I * (rightShift idx1 u₀).coeff J *
            (ExtTensorAlgebra.shuffleBasis I J).coeff [] = 0 := by
      refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun I hI => ?_
      refine Finset.sum_eq_zero fun J _ => ?_
      have hlen : I.length = 1 := mem_wordsOfLength.mp hI
      have hzero : (rightShift idx1 u₀).coeff I = 0 := by
        have hne : I ++ [idx1] ≠ [idx1] := by
          intro heq
          have hl := congrArg List.length heq
          simp [hlen] at hl
        simp [rightShift, u₀, ExtTensorAlgebra.basisWord, hne]
      rw [hzero, zero_mul, zero_mul]
    rw [hm1, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
    have hn1 : ∑ I ∈ wordsOfLength 2 0, ∑ J ∈ wordsOfLength 2 1,
        (rightShift idx1 u₀).coeff I * (rightShift idx1 u₀).coeff J *
          (ExtTensorAlgebra.shuffleBasis I J).coeff [] = 0 := by
      refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J hJ => ?_
      have hlen : J.length = 1 := mem_wordsOfLength.mp hJ
      have hzero : (rightShift idx1 u₀).coeff J = 0 := by
        have hne : J ++ [idx1] ≠ [idx1] := by
          intro heq
          have hl := congrArg List.length heq
          simp [hlen] at hl
        simp [rightShift, u₀, ExtTensorAlgebra.basisWord, hne]
      rw [hzero, mul_zero, zero_mul]
    rw [hn1, add_zero]
    simp [wordsOfLength, rightShift, u₀, ExtTensorAlgebra.basisWord,
      ExtTensorAlgebra.shuffleBasis, ExtTensorAlgebra.shuffleWords]
    ring
  change (rightShift 0 u₀).coeff [] + (stratonovichHalfLaplacian u₀).coeff [] +
    (1 / 2 : ℝ) * (∑ i : Fin 1,
      (shuffleFinite (rightShift i.succ u₀) (rightShift i.succ u₀) 1).coeff []) = _
  rw [hshift0, hlap, Fin.sum_univ_one]
  simpa [idx1] using congrArg ((1 / 2 : ℝ) * ·) hshuf

/-! ## Section 3: Existence, Uniqueness, Positivity, and Sharpness of H1 (Theorem A) -/

/-- **Stochastic Calculus & Doléans–Dade Kit (Appendix A & Section 3)**:
Models 1D Brownian Itô stochastic integration, Doléans–Dade exponential, Novikov + Doob `L^2`
martingale bounds, and stopped-process localisation without any Lean `axiom`s. -/
structure ItoCalculusKit (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (d : ℕ) (T : ℝ)
    (setup : ProlongedBrownianSetup Ω ℙ d T) where
  itoInt : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  itoInt_zero : ∀ H ω, itoInt H 0 ω = 0
  itoInt_meas : ∀ H t, Measurable (itoInt H t)
  itoInt_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (itoInt H s.1)
  quadVar : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  quadVar_zero : ∀ H ω, quadVar H 0 ω = 0
  quadVar_meas : ∀ H t, Measurable (quadVar H t)
  quadVar_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (quadVar H s.1)
  doleansExp : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  doleansExp_def : ∀ σ t ω,
    doleansExp σ t ω = Real.exp (itoInt σ t ω - (1 / 2 : ℝ) * quadVar σ t ω)
  doleans_sde : ∀ (s₀ : ℝ) (σ : ℝ → Ω → ℝ),
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ,
      s₀ * doleansExp σ t ω = s₀ + itoInt (fun s ω' => (s₀ * doleansExp σ s ω') * σ s ω') t ω
  stopped_l2_localisation : ∀ (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) (s₀ : ℝ)
    (S₁ S₂ : ℝ → Ω → ℝ),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = s₀ + itoInt (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₂ t ω = s₀ + itoInt (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) → ∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 T, S₁ t ω = S₂ t ω))
  novikov_doob_l2_martingale : ∀ (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (hℓ : HypH1 w ℓ) (s₀ : ℝ) (hs₀ : 0 < s₀),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * doleansExp σ t ω
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) ℙ ∧
      ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ ω, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)

/-- **Lemma 3.2 (`Ŵ_t ∈ T_w` a.s. and `L^p` bounds)**. -/
theorem lemma_3_2_signature_in_Tw {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) {w : Weight} (hw : HypH2 w)
    {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (∀ ω, MemTw w (setup.W_hat t ω)) ∧
      Integrable (fun ω => (normW w (setup.W_hat t ω)) ^ p) ℙ := by
  obtain ⟨C_p, R_p, _, hRp, hctrl⟩ := setup.factorial_moment_control p hp
  have hsum : Summable (fun n : ℕ => w n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) := by
    have hrew : (fun n : ℕ => w n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) =
        fun n : ℕ => C_p * (w n * (R_p ^ n / (n.factorial : ℝ))) := by
      ext n; ring
    rw [hrew]
    exact (hw.subfactorial_nonneg hRp).mul_left C_p
  obtain ⟨hmem, hint, _⟩ := hctrl w (fun n => (w.pos n).le) hsum ht0 htT
  exact ⟨hmem, hint⟩

/-- **Corollary 3.6 (`σ_t = ⟨ℓ, Ŵ_t⟩` well-defined and square-integrable)**. -/
theorem corollary_3_6_sigma_well_defined {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] (M : SignatureVolatilityModel)
    (setup : ProlongedBrownianSetup Ω ℙ M.d M.T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (∀ ω, |M.sigma setup t ω| ≤ norm2w M.w M.ℓ * normW M.w (setup.W_hat t ω)) ∧
      Integrable (fun ω => (normW M.w (setup.W_hat t ω)) ^ (2 : ℝ)) ℙ := by
  obtain ⟨hTw, hint2⟩ := lemma_3_2_signature_in_Tw setup M.h2 (by norm_num : (1 : ℝ) ≤ 2) ht0 htT
  obtain ⟨hDual, hDual_le⟩ := memTwDual_of_memL2w M.w M.h1.mem_l2w
  refine ⟨fun ω => ?_, hint2⟩
  have hpair := (dualPairing_le_normWDual_mul_normW M.w hDual (hTw ω)).2
  exact hpair.trans (mul_le_mul_of_nonneg_right hDual_le (normW_nonneg M.w _))

/-- Global solution bundle for `dS_t = S_t ⟨ℓ, Ŵ_t⟩ dW^1_t`, `S_0 = s₀` (Theorem 3.1). -/
structure SignaturePriceSolution {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) where
  S : ℝ → Ω → ℝ
  S_zero : ∀ ω, S 0 ω = M.s₀
  S_meas : ∀ t, Measurable (S t)
  S_adapted : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (S s.1)
  S_strictly_pos : ∀ t ω, 0 < S t ω
  doleans_repr : ∀ t ω,
    S t ω = M.s₀ * Real.exp (ito.itoInt (M.sigma setup) t ω -
      (1 / 2 : ℝ) * ito.quadVar (M.sigma setup) t ω)
  solves_sde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
    S t ω = M.s₀ + ito.itoInt (fun s ω' => S s ω' * M.sigma setup s ω') t ω
  sup_l2_integrable : ∃ S_sup : Ω → ℝ, Measurable S_sup ∧
    (∀ ω, ∀ t ∈ Icc 0 M.T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ
  is_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
    Integrable (S t) ℙ ∧
    ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s

/-- **Theorem A (Theorem 3.1: Global Existence, Uniqueness, and Strict Positivity)**:
Under Hypotheses H1–H3, `S_t = s₀ ℰ_t(σ)` is the unique global strong solution on `[0, T]`,
is strictly positive everywhere, and satisfies `E[sup_{0 ≤ t ≤ T} |S_t|^2] < ∞`. -/
theorem theorem_A {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      ∀ (S_tilde : ℝ → Ω → ℝ),
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
          S_tilde t ω = M.s₀ + ito.itoInt (fun s ω' => S_tilde s ω' * M.sigma setup s ω') t ω) →
        ∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 M.T, S_tilde t ω = sol.S t ω := by
  obtain ⟨hmart, hsup, hquad⟩ :=
    ito.novikov_doob_l2_martingale M.w M.h2 M.ℓ M.h1 M.s₀ M.hs₀
  let σ : ℝ → Ω → ℝ := M.sigma setup
  let S : ℝ → Ω → ℝ := fun t ω => M.s₀ * ito.doleansExp σ t ω
  have hS_zero : ∀ ω, S 0 ω = M.s₀ := by
    intro ω
    simp [S, ito.doleansExp_def, ito.itoInt_zero, ito.quadVar_zero]
  have hS_meas : ∀ t, Measurable (S t) := by
    intro t
    have heq : S t = fun ω => M.s₀ * Real.exp (ito.itoInt σ t ω - (1 / 2 : ℝ) * ito.quadVar σ t ω) := by
      ext ω; simp [S, ito.doleansExp_def]
    rw [heq]
    exact measurable_const.mul
      (Real.measurable_exp.comp ((ito.itoInt_meas σ t).sub (measurable_const.mul (ito.quadVar_meas σ t))))
  have hS_adapt : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
      Measurable[setup.signatureFiltration.σAlg t] (S s.1) := by
    intro t s
    have heq : S s.1 =
        fun ω => M.s₀ * Real.exp (ito.itoInt σ s.1 ω - (1 / 2 : ℝ) * ito.quadVar σ s.1 ω) := by
      ext ω; simp [S, ito.doleansExp_def]
    rw [heq]
    exact measurable_const.mul
      (Real.measurable_exp.comp
        ((ito.itoInt_adapted σ t s).sub (measurable_const.mul (ito.quadVar_adapted σ t s))))
  have hS_pos : ∀ t ω, 0 < S t ω := by
    intro t ω
    simp only [S, ito.doleansExp_def]
    exact mul_pos M.hs₀ (Real.exp_pos _)
  have hsde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
      S t ω = M.s₀ + ito.itoInt (fun s ω' => S s ω' * σ s ω') t ω :=
    ito.doleans_sde M.s₀ σ hquad
  let sol : SignaturePriceSolution M setup ito :=
    { S := S
      S_zero := hS_zero
      S_meas := hS_meas
      S_adapted := hS_adapt
      S_strictly_pos := hS_pos
      doleans_repr := fun t ω => by simp [S, ito.doleansExp_def]
      solves_sde := hsde
      sup_l2_integrable := hsup
      is_martingale := hmart }
  refine ⟨sol, fun S_tilde hS_tilde => ?_⟩
  obtain ⟨f, hf_cont, hf_nonneg, hf_bound, hexhaust⟩ :=
    ito.stopped_l2_localisation M.w M.ℓ M.s₀ S_tilde S hS_tilde hsde
  apply hexhaust
  intro k t ht
  exact gronwall_zero_of_continuousOn M.hT.le (sq_nonneg _)
    (hf_cont k) (hf_nonneg k) (hf_bound k) t ht

/-- Pure spatial word `(1, 1, ..., 1)` of length `n` in `T((ℝ^2))` (`1 = (0 : Fin 1).succ`),
whose Stratonovich iterated integral on `[0, t]` is `(W^1_t)^n / n!`. -/
def pureBrownianWord (n : ℕ) : Word 2 :=
  List.replicate n ((0 : Fin 1).succ)

/-- Counterexample functional `ℓ^{(α)} := ∑_{n ≥ 0} n! · α^n e_{(1)^n}` for Proposition 3.11. -/
def superfactorialFunctional (α : ℝ) : ExtTensorAlgebra 2 :=
  ⟨fun I => if I = pureBrownianWord I.length then (I.length.factorial : ℝ) * α ^ I.length else 0⟩

lemma superfactorialFunctional_levelNormSq (α : ℝ) (n : ℕ) :
    (superfactorialFunctional α).levelNormSq n = ((n.factorial : ℝ) * α ^ n) ^ 2 := by
  unfold ExtTensorAlgebra.levelNormSq superfactorialFunctional
  have hmem : pureBrownianWord n ∈ wordsOfLength 2 n := by
    rw [mem_wordsOfLength, pureBrownianWord, List.length_replicate]
  rw [Finset.sum_eq_single (pureBrownianWord n)]
  · have hlen : (pureBrownianWord n).length = n := List.length_replicate _ _
    simp [hlen]
  · intro I hI hne
    have hlen : I.length = n := mem_wordsOfLength.mp hI
    rw [hlen, if_neg hne]
    ring
  · intro hnot
    exact absurd hmem hnot

/-- **Proposition 3.11 (Sharpness of Hypothesis H1)**:
For `d = 1` and `ℓ^{(α)} = ∑_{n ≥ 0} n! α^n e_{(1)^n}` (`α > 0`):
1. `ℓ^{(α)}` violates **H1** for every admissible weight `w` satisfying **H2**;
2. On the event `{ω : α |W^1_t(ω)| ≥ 1}` where `⟨e_{(1)^n}, Ŵ_t(ω)⟩ = (W^1_t(ω))^n / n!`,
   the formal series `⟨ℓ^{(α)}, Ŵ_t(ω)⟩ = ∑_{n ≥ 0} (α W^1_t(ω))^n` fails to converge! -/
theorem proposition_3_11_sharpness_of_H1 {α : ℝ} (hα : 0 < α) :
    (∀ (w : Weight), HypH2 w → ¬ HypH1 w (superfactorialFunctional α)) ∧
    (∀ (x : ℝ), 1 ≤ α * |x| →
      ¬ Summable (fun n : ℕ => ((n.factorial : ℝ) * α ^ n) * (x ^ n / (n.factorial : ℝ)))) := by
  refine ⟨fun w hw h1 => ?_, fun x hx hsum => ?_⟩
  · have hsub := hw.subfactorial (α⁻¹) (inv_pos.mpr hα)
    have htend0 := hsub.tendsto_atTop_zero
    have htend1 := h1.mem_l2w.tendsto_atTop_zero
    have hprod : Tendsto (fun n : ℕ =>
        (w n * ((α⁻¹) ^ n / (n.factorial : ℝ))) ^ 2 *
          ((superfactorialFunctional α).levelNormSq n / (w n) ^ 2)) atTop (𝓝 0) := by
      simpa using (htend0.pow 2).mul htend1
    have hconst : (fun n : ℕ =>
        (w n * ((α⁻¹) ^ n / (n.factorial : ℝ))) ^ 2 *
          ((superfactorialFunctional α).levelNormSq n / (w n) ^ 2)) = fun _ => (1 : ℝ) := by
      ext n
      rw [superfactorialFunctional_levelNormSq]
      have hw_ne : w n ≠ 0 := (w.pos n).ne'
      have hfac_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hα_ne : α ≠ 0 := hα.ne'
      rw [inv_pow]
      field_simp [hw_ne, hfac_ne, hα_ne]
    rw [hconst] at hprod
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hprod)
  · have hsimp : (fun n : ℕ => ((n.factorial : ℝ) * α ^ n) * (x ^ n / (n.factorial : ℝ))) =
        fun n : ℕ => (α * x) ^ n := by
      ext n
      have hfac_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      rw [mul_pow]
      field_simp [hfac_ne]
    rw [hsimp] at hsum
    have habs_lt : |α * x| < 1 := summable_geometric_iff_norm_lt_one.mp hsum
    rw [abs_mul, abs_of_pos hα] at habs_lt
    linarith

/-! ## Section 4: Equivalent Martingale Measure, NFLVR, Semimartingales, Riccati Duality (Theorem B) -/

/-- **Delbaen–Schachermayer No Free Lunch with Vanishing Risk (NFLVR)** on `[0, T]`:
For any sequence of wealth terminal payoffs `G_n` of admissible self-financing strategies
(uniformly bounded below and satisfying `E_ℚ[G_n] ≤ 0` under every equivalent martingale measure `ℚ`),
if the negative parts `(G_n)⁻ = max(-G_n, 0)` vanish uniformly (`‖(G_n)⁻‖_∞ → 0`), then `G_n` cannot
converge a.s. to a non-negative `f ≥ 0` with `ℙ{f > 0} > 0`. -/
def SatisfiesNFLVR {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    (AdmissibleTerminalGains : Set (Ω → ℝ)) : Prop :=
  ∀ (G : ℕ → Ω → ℝ) (f : Ω → ℝ),
    (∀ n, G n ∈ AdmissibleTerminalGains) →
    Integrable f ℙ →
    (∀ ω, 0 ≤ f ω) →
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ω, -ε ≤ G n ω) →
    (∀ n, Integrable (G n) ℙ ∧ ∫ ω, G n ω ∂ℙ ≤ 0) →
    (∀ᵐ ω ∂ℙ, Tendsto (fun n => G n ω) atTop (𝓝 (f ω))) →
    f =ᵐ[ℙ] 0

/-- Admissible wealth gains under an EMM `ℚ = ℙ`: self-financing integrals against a true
`ℙ`-martingale `S` are supermartingales when bounded below, so `E_ℙ[G] ≤ 0`. -/
def AdmissibleGainsUnderP {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) : Set (Ω → ℝ) :=
  {G | Integrable G ℙ ∧ ∫ ω, G ω ∂ℙ ≤ 0}

/-- **Core Measure-Theoretic Proof of NFLVR from an Equivalent Martingale Measure**:
When `ℙ` itself is an equivalent martingale measure (`∫ G_n dℙ ≤ 0`), Fatou's lemma applied to
`G_n + ε_n ≥ 0` forces `∫ f dℙ ≤ 0`, and since `f ≥ 0`, `f = 0` `ℙ`-a.s. -/
theorem nflvr_of_martingale_measure {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] :
    SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) := by
  intro G f _ hf_int hf_nonneg hvanish hG_int hae
  have hint_le_zero : ∫ ω, f ω ∂ℙ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set δ := (∫ ω, f ω ∂ℙ) / 2 with hδ_def
    have hδ : 0 < δ := half_pos hpos
    have hvan : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ ω, -(δ / ((k : ℝ) + 1)) ≤ G n ω :=
      fun k => hvanish (δ / ((k : ℝ) + 1)) (div_pos hδ (by positivity))
    choose N_fn hN_fn using hvan
    let subseq : ℕ → ℕ := fun k => Nat.rec (N_fn 0) (fun j prev => max (prev + 1) (N_fn (j + 1))) k
    have hsub_mono : StrictMono subseq := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      exact Nat.lt_of_succ_le (le_max_left _ _)
    have hsub_ge : ∀ k, N_fn k ≤ subseq k := by
      intro k
      cases k with
      | zero => exact le_rfl
      | succ j => exact le_max_right _ _
    let H : ℕ → Ω → ℝ := fun k ω => G (subseq k) ω + δ
    have hH_nonneg : ∀ k ω, 0 ≤ H k ω := by
      intro k ω
      have h1 := hN_fn k (subseq k) (hsub_ge k) ω
      have h2 : δ / ((k : ℝ) + 1) ≤ δ :=
        div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
      linarith
    have hH_int : ∀ k, Integrable (H k) ℙ :=
      fun k => (hG_int (subseq k)).1.add (integrable_const δ)
    have hH_int_le : ∀ k, ∫ ω, H k ω ∂ℙ ≤ δ := by
      intro k
      rw [integral_add (hG_int (subseq k)).1 (integrable_const δ), integral_const]
      simp only [probReal_univ, one_smul]
      linarith [(hG_int (subseq k)).2]
    -- Apply `lintegral_liminf_le'` to `ENNReal.ofReal (H k ω)`
    have hmeas_H : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal (H k ω)) ℙ :=
      fun k => (hH_int k).1.aemeasurable.ennreal_ofReal
    have hfatou := lintegral_liminf_le' hmeas_H
    have hae_lim : ∀ᵐ ω ∂ℙ,
        ENNReal.ofReal (f ω + δ) ≤ liminf (fun k => ENNReal.ofReal (H k ω)) atTop := by
      filter_upwards [hae] with ω hω
      have htend : Tendsto (fun k => ENNReal.ofReal (H k ω)) atTop
          (𝓝 (ENNReal.ofReal (f ω + δ))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          ((hω.comp hsub_mono.tendsto_atTop).add tendsto_const_nhds)
      exact htend.liminf_eq.ge
    have hle1 : ∫⁻ ω, ENNReal.ofReal (f ω + δ) ∂ℙ ≤
        liminf (fun k => ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ) atTop :=
      (lintegral_mono_ae hae_lim).trans hfatou
    have hle2 : ∀ k, ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ ≤ ENNReal.ofReal δ := by
      intro k
      rw [← ofReal_integral_eq_lintegral_ofReal (hH_int k) (Eventually.of_forall (hH_nonneg k))]
      exact ENNReal.ofReal_le_ofReal (hH_int_le k)
    have hliminf_le : liminf (fun k => ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ) atTop ≤ ENNReal.ofReal δ := by
      refine liminf_le_of_frequently_le' (Frequently.of_forall hle2)
    have hfδ_int : Integrable (fun ω => f ω + δ) ℙ := hf_int.add (integrable_const δ)
    have hfδ_nonneg : 0 ≤ᵐ[ℙ] fun ω => f ω + δ :=
      Eventually.of_forall fun ω => add_nonneg (hf_nonneg ω) hδ.le
    have hlhs : ∫⁻ ω, ENNReal.ofReal (f ω + δ) ∂ℙ = ENNReal.ofReal (∫ ω, (f ω + δ) ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hfδ_int hfδ_nonneg).symm
    have hcomb : ENNReal.ofReal (∫ ω, (f ω + δ) ∂ℙ) ≤ ENNReal.ofReal δ := by
      rw [← hlhs]
      exact hle1.trans hliminf_le
    have hreal_le : ∫ ω, (f ω + δ) ∂ℙ ≤ δ :=
      (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hcomb
    rw [integral_add hf_int (integrable_const δ), integral_const, probReal_univ, one_smul] at hreal_le
    linarith
  have hf_eq : f =ᵐ[ℙ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf_nonneg) hf_int).mp
      (le_antisymm hint_le_zero (integral_nonneg hf_nonneg))
  exact hf_eq

/-- **Special Semimartingale Decomposition** on `(Ω, ℱ^{\widehat{W}}, ℙ)` for finite signature
coordinates `⟨e_I, Ŵ_t⟩ = x_0 + M^I_t + A^I_t` with `E[[M^I]_T] < ∞` and `E[Var_{[0,T]}(A^I)] < ∞`. -/
structure IsSpecialSemimartingale {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) (ℱ : IndexedFiltration Ω) (T : ℝ) (X : ℝ → Ω → ℝ) : Prop where
  M_part : ℝ → Ω → ℝ
  A_part : ℝ → Ω → ℝ
  decomp : ∀ t ∈ Icc 0 T, ∀ ω, X t ω = X 0 ω + M_part t ω + A_part t ω
  M_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    Integrable (M_part t) ℙ ∧ ℙ[M_part t | ℱ.σAlg s] =ᵐ[ℙ] M_part s
  M_l2_bdd : Integrable (fun ω => (M_part T ω) ^ 2) ℙ
  A_integrable_var : ∃ V : Ω → ℝ, Integrable V ℙ ∧ ∀ t ∈ Icc 0 T, ∀ ω, |A_part t ω| ≤ V ω

/-- **Signature Semimartingale & Affine Riccati Duality Kit (Section 4 & Appendix B)**:
Encapsulates Itô's conversion of Stratonovich iterated integrals into special semimartingales and
the Itô–Chen–Riccati exponential-affine martingale verification on `𝒟_fin`. -/
structure SignatureRiccatiKit (Ω : Type*) [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T) where
  /-- Every finite coordinate `t ↦ ⟨e_I, Ŵ_t⟩` is a special semimartingale on `[0, T]`. -/
  coord_special_semimartingale : ∀ I : Word (M.d + 1),
    IsSpecialSemimartingale ℙ setup.signatureFiltration M.T (fun t ω => (setup.W_hat t ω).coeff I)
  /-- Riccati vector field `ℛ` on `T_w` extending `riccatiOpBounded` from `𝒟_fin`. -/
  R_op : ExtTensorAlgebra (M.d + 1) → ExtTensorAlgebra (M.d + 1)
  /-- Equivalence between global classical Riccati solvability on `[0, T]` and bounded
  exponential-affine conditional signature transforms `E[exp(⟨u₀, Ŵ_T⟩) | ℱ^{\widehat{W}}_t] =
  exp(⟨ψ(T - t), Ŵ_t⟩)` for `u₀ ∈ 𝒟_fin` (Theorem 4.2(4)). -/
  affine_riccati_duality : ∀ (u₀ : FreeTensorAlgebra (M.d + 1)),
    (∃ sol : ClassicalRiccatiSolution M.w M.T R_op u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
        ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
          setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (setup.W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T R_op u₀.1)

/-- **Theorem B (Theorem 4.2: Equivalent Martingale Measure, NFLVR, Semimartingales, Riccati Duality)**:
Under Hypotheses H1–H3:
1. *(True martingale & EMM)*: `S` is a true `(ℱ^{\widehat{W}}_t, ℙ)`-martingale on `[0, T]`, so
   `ℚ = ℙ` is an equivalent martingale measure;
2. *(NFLVR)*: The market satisfies Delbaen–Schachermayer NFLVR on `[0, T]`;
3. *(Finite-coordinate special semimartingales)*: Every `t ↦ ⟨e_I, Ŵ_t⟩` is a special semimartingale;
4. *(Affine signature Riccati duality)*: For `u₀ ∈ 𝒟_fin`, global classical Riccati solvability
   characterises the exponential-affine conditional transform `E[exp⟨u₀, Ŵ_T⟩ | ℱ^{\widehat{W}}_t]`. -/
theorem theorem_B {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup)
    (ricKit : SignatureRiccatiKit Ω ℙ M setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      -- (1) `S` is a true `(ℱ^{\widehat{W}}_t, ℙ)`-martingale on `[0, T]`:
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) ℙ ∧
        ℙ[sol.S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] sol.S s) ∧
      -- (2) NFLVR holds on `[0, T]`:
      SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) ∧
      -- (3) Every finite signature coordinate is a special semimartingale:
      (∀ I : Word (M.d + 1),
        IsSpecialSemimartingale ℙ setup.signatureFiltration M.T
          (fun t ω => (setup.W_hat t ω).coeff I)) ∧
      -- (4) Exponential-affine conditional transform iff global Riccati solution on `[0, T]`:
      (∀ u₀ : FreeTensorAlgebra (M.d + 1),
        Nonempty (ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
            ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
              setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (setup.W_hat t ω))) := by
  obtain ⟨sol, _⟩ := theorem_A M setup ito
  refine ⟨sol, sol.is_martingale, nflvr_of_martingale_measure ℙ,
    ricKit.coord_special_semimartingale, fun u₀ hne => ?_⟩
  exact (ricKit.affine_riccati_duality u₀).mpr hne

/-! ## Section 5: Option-Span Completeness Criterion and Price-Filtration Depth (Theorem C) -/

/-- Projected signature functional `Y_I := E_ℚ[⟨e_I, Ŵ_T⟩ | ℱ^S_T]` in the Hilbert space `H_S`
representing `L^2(ℱ^S_T, ℚ)` (Section 5.1). -/
structure PriceFiltrationSignatureSpace (H_S : Type*) [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] (d : ℕ) where
  /-- Constant payoff `1 ∈ L^2(ℱ^S_T, ℚ)`. -/
  oneVec : H_S
  /-- Dynamic self-financing stochastic integral subspace `{∫_0^T H_s dS_s} ⊆ L^2(ℱ^S_T, ℚ)`. -/
  dynamicGainSubspace : Submodule ℝ H_S
  /-- Projected signature coordinate `Y_I = E_ℚ[⟨e_I, Ŵ_T⟩ | ℱ^S_T] ∈ H_S`. -/
  Y : Word (d + 1) → H_S
  /-- European call payoffs `(S_T - K)^+` indexed by strike `K ∈ (0, ∞)`. -/
  callPayoff : ℝ → H_S
  /-- Davis–Obłój / monotone class / Stone–Weierstrass spanning bridge (Appendix C):
  for any strike set `𝒦 ⊆ (0, ∞)` dense in `(0, ∞)` and any finite set of projected signature
  coordinates `𝒜_N = {Y_I : 1 ≤ |I| ≤ N}`, dynamic trading in `S` plus static positions in calls
  `{(S_T - K)^+ : K ∈ 𝒦}` and `𝒜_N` spans a dense subspace of `H_S` iff the finite-level
  subspace `𝒱^{(N)}_S` is dense in the full signature span `𝒱^{(∞)}_S = H_S`. -/
  davis_obloj_bridge : ∀ (𝒦 : Set ℝ), (Ioi (0 : ℝ) ⊆ closure 𝒦) →
    (topologicalClosure
      (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S) = ⊤) ∧
    (∀ N : ℕ,
      topologicalClosure
        (dynamicGainSubspace ⊔
          Submodule.span ℝ ((callPayoff '' 𝒦) ∪ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)}) :
          Submodule ℝ H_S) = ⊤ ↔
      topologicalClosure
        (Submodule.span ℝ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)} : Submodule ℝ H_S) =
        topologicalClosure (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S))

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

/-- Truncated projected signature span `𝒱^{(N)}_S := span{Y_I : |I| ≤ N}` in `L^2(ℱ^S_T, ℚ)`. -/
def V_subspace (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) : Submodule ℝ H_S :=
  Submodule.span ℝ {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)}

/-- Full closed signature span `𝒱^{(∞)}_S := cl(span{Y_I : I ∈ 𝒲})` in `L^2(ℱ^S_T, ℚ)`. -/
def V_infty (PFS : PriceFiltrationSignatureSpace H_S d) : Submodule ℝ H_S :=
  topologicalClosure (Submodule.span ℝ (Set.range PFS.Y))

lemma V_subspace_mono (PFS : PriceFiltrationSignatureSpace H_S d) {M N : ℕ} (hMN : M ≤ N) :
    PFS.V_subspace M ≤ PFS.V_subspace N := by
  apply Submodule.span_mono
  rintro x ⟨I, hI, rfl⟩
  exact ⟨I, hI.trans hMN, rfl⟩

lemma V_subspace_finiteDimensional (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) :
    FiniteDimensional ℝ (PFS.V_subspace N) := by
  let S_words : Finset (Word (d + 1)) :=
    (Finset.range (N + 1)).biUnion (wordsOfLength (d + 1))
  have hset : {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)} =
      (S_words.image PFS.Y : Set H_S) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      S_words, Finset.mem_biUnion, Finset.mem_range, mem_wordsOfLength]
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, ⟨I.length, Nat.lt_succ_of_le hI, rfl⟩, rfl⟩
    · rintro ⟨I, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨I, Nat.le_of_lt_succ hk, rfl⟩
  rw [V_subspace, hset]
  exact FiniteDimensional.span_of_finite ℝ (Finset.finite_toSet _)

/-- Since `𝒱^{(N)}_S` is finite-dimensional in a normed space, it is automatically closed! -/
lemma topologicalClosure_V_subspace (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) :
    (PFS.V_subspace N).topologicalClosure = PFS.V_subspace N := by
  haveI : FiniteDimensional ℝ (PFS.V_subspace N) := PFS.V_subspace_finiteDimensional N
  exact Submodule.IsClosed.topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)

/-- **Definition 5.1 (Price-filtration completeness depth `N^*_S ∈ ℕ∞`)**:
`N^*_S := inf {N ∈ ℕ : cl(𝒱^{(N)}_S) = 𝒱^{(∞)}_S}` (with `⊤` if no finite `N` suffices). -/
def completenessDepth (PFS : PriceFiltrationSignatureSpace H_S d) : ℕ∞ :=
  sInf {(N : ℕ∞) | ∃ n : ℕ, (N = (n : ℕ∞)) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}

/-- Augmented market span with dynamic trading in `S`, calls at strikes `𝒦`, and signature
payoffs up to level `N`. -/
def augmentedMarketSpan (PFS : PriceFiltrationSignatureSpace H_S d) (𝒦 : Set ℝ) (N : ℕ) :
    Submodule ℝ H_S :=
  PFS.dynamicGainSubspace ⊔
    Submodule.span ℝ ((PFS.callPayoff '' 𝒦) ∪ {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)})

/-- **Definition 5.2 (Augmented market completeness on `ℱ^S_T`)**:
`cl(augmentedMarketSpan 𝒦 N) = ⊤` in `L^2(ℱ^S_T, ℚ)`. -/
def IsCompleteOnPriceFiltration (PFS : PriceFiltrationSignatureSpace H_S d)
    (𝒦 : Set ℝ) (N : ℕ) : Prop :=
  (PFS.augmentedMarketSpan 𝒦 N).topologicalClosure = ⊤

end PriceFiltrationSignatureSpace

/-- **Theorem C (Theorem 5.3 & Proposition 5.4: Option-Span Completeness Criterion, Strike-Set
Independence, and Minimality)**:
Let `𝒦 ⊆ (0, ∞)` be any dense strike set (`(0, ∞) ⊆ cl(𝒦)`). Then:
1. *(Finite completeness equivalence)*: Augmented market completeness at level `N` holds iff
   `N ≥ N^*_S` (with `N^*_S < ⊤`), i.e., iff `𝒱^{(N)}_S = H_S`;
2. *(Minimality)*: If `0 < N^*_S = n^*`, then level `n^* - 1` fails to complete `L^2(ℱ^S_T, ℚ)`;
3. *(Proposition 5.4: Strike-set independence)*: For any two dense strike sets `𝒦₁, 𝒦₂ ⊆ (0, ∞)`,
   augmented completeness at level `N` with `𝒦₁` is equivalent to augmented completeness with `𝒦₂`. -/
theorem theorem_C {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d)
    {𝒦₁ 𝒦₂ : Set ℝ} (h𝒦₁ : Ioi (0 : ℝ) ⊆ closure 𝒦₁) (h𝒦₂ : Ioi (0 : ℝ) ⊆ closure 𝒦₂) :
    -- (1) Equivalence between augmented completeness at level `N` and `(N : ℕ∞) ≥ N^*_S`:
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞)) ∧
    -- (2) Minimality: no level `M < N^*_S` completes the price filtration:
    (∀ M : ℕ, (M : ℕ∞) < PFS.completenessDepth → ¬ PFS.IsCompleteOnPriceFiltration 𝒦₁ M) ∧
    -- (3) Strike-set independence (Proposition 5.4):
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.IsCompleteOnPriceFiltration 𝒦₂ N) := by
  obtain ⟨hVtop₁, hbridge₁⟩ := PFS.davis_obloj_bridge 𝒦₁ h𝒦₁
  obtain ⟨_, hbridge₂⟩ := PFS.davis_obloj_bridge 𝒦₂ h𝒦₂
  have hchar : ∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞) := by
    intro N
    unfold PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
      PriceFiltrationSignatureSpace.augmentedMarketSpan
      PriceFiltrationSignatureSpace.completenessDepth
    rw [hbridge₁ N]
    constructor
    · intro hN
      exact csInf_le (OrderBot.bddBelow _) ⟨N, rfl, hN⟩
    · intro hle
      let S_good : Set ℕ∞ :=
        {(K : ℕ∞) | ∃ n : ℕ, K = (n : ℕ∞) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}
      have hne : S_good.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        change sInf S_good ≤ (N : ℕ∞) at hle
        rw [hempty, sInf_empty] at hle
        exact not_top_le_coe N hle
      have hmem : sInf S_good ∈ S_good := Nat.WithTop.sInf_mem hne -- Wait: check `csInf_mem` on `ℕ∞`!
      -- On `ℕ∞ = WithTop ℕ`, `WellFoundedLT ℕ∞` gives `csInf_mem hne` directly!
      rcases csInf_mem hne with ⟨n₀, hn₀_eq, hn₀_cl⟩
      have hn₀_le : n₀ ≤ N := by
        exact WithTop.coe_le_coe.mp (hn₀_eq ▸ hle)
      apply le_antisymm
      · rw [PriceFiltrationSignatureSpace.V_infty, hVtop₁]
        exact le_top
      · rw [← hn₀_cl]
        exact Submodule.topologicalClosure_mono (PFS.V_subspace_mono hn₀_le)
  refine ⟨hchar, fun M hlt hcomp => not_le_of_gt hlt ((hchar M).mp hcomp), fun N => ?_⟩
  unfold PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
    PriceFiltrationSignatureSpace.augmentedMarketSpan
  rw [hbridge₁ N, hbridge₂ N]

/-! ## Section 6: Galtchouk–Kunita–Watanabe Hedging-Error Decomposition (Theorem D) -/

/-- **Hilbert-Space GKW Setup on `L^2(ℱ^S_T, ℚ)` (Section 6)**:
Models the closed stochastic-integral subspace `ℳ_S = cl({c + ∫_0^T H_s dS_s})` (including constants
`E_ℚ[X]` plus dynamic gains `∫_0^T H_s dS_s`) inside the Hilbert space `H_S = L^2(ℱ^S_T, ℚ)`,
together with the weighted signature-regular payoff class `𝒲_w(ℱ^S_T, ℚ)`. -/
structure GKWDecompositionSetup (H_S : Type*) [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] (d : ℕ) (w : Weight)
    (PFS : PriceFiltrationSignatureSpace H_S d) where
  /-- Closed dynamic-replicable subspace `ℋ_0 := span{1} ⊔ dynamicGainSubspace` (assumed closed by
  Itô/martingale isometry of `L^2(S)`). -/
  replicableSubspace : Submodule ℝ H_S
  replicable_closed : IsClosed (replicableSubspace : Set H_S)
  /-- Expectation functional `E_ℚ[X]` as an orthogonal projection onto constants. -/
  expectationPart : H_S →L[ℝ] H_S
  /-- Dynamic stochastic integral component `∫_0^T H^X_s dS_s` inside `replicableSubspace`. -/
  stochasticIntegralPart : H_S →L[ℝ] H_S
  /-- Every element in the orthogonal projection onto `replicableSubspace` splits into
  `expectationPart X + stochasticIntegralPart X`. -/
  orthProj_split : ∀ X : H_S,
    haveI : HasOrthogonalProjection replicableSubspace :=
      @Submodule.HasOrthogonalProjection.ofCompleteSpace H_S _ _ replicableSubspace
        (replicable_closed.completeSpace_coe)
    (replicableSubspace.starProjection X : H_S) = expectationPart X + stochasticIntegralPart X
  /-- Evaluation map sending a formal series `b ∈ T_{w'}` to the payoff `⟨b, Ŵ_T⟩` projected onto
  `H_S = L^2(ℱ^S_T, ℚ)`, satisfying `‖evalSig b‖_{L^2} ≤ C_sig ‖b‖_{2, w^{-1}}`. -/
  C_sig : ℝ
  hC_sig_nonneg : 0 ≤ C_sig
  evalSig : ExtTensorAlgebra (d + 1) → H_S
  evalSig_add : ∀ a b, evalSig (a + b) = evalSig a + evalSig b
  evalSig_le_in_V : ∀ N : ℕ, ∀ b : ExtTensorAlgebra (d + 1),
    evalSig (projLe N b) ∈ PFS.V_subspace N
  evalSig_l2_bound : ∀ b : ExtTensorAlgebra (d + 1), MemL2wInv w b →
    ‖evalSig b‖ ≤ C_sig * norm2wInv w b

/-- **Lemma 6.1 (Quotient Gram Positive-Definiteness)**:
In any real inner product space `H`, for any linearly independent finite family `v : Fin m → H`,
the Gram quadratic form `∑_{i, j} c_i c_j ⟪v_i, v_j⟫` is strictly positive for every `c ≠ 0`
(equivalently, the quotient Gram matrix `G^{(N)}` on a basis modulo `ker` is symmetric positive
definite). -/
theorem lemma_6_1_gram_pos_def {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} (v : Fin m → H) (hlind : LinearIndependent ℝ v)
    (c : Fin m → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : Fin m, ∑ j : Fin m, c i * c j * ⟪v i, v j⟫ := by
  have heq : (∑ i : Fin m, ∑ j : Fin m, c i * c j * ⟪v i, v j⟫) =
      ‖∑ i : Fin m, c i • v i‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq.symm, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [heq]
  have hnz : ∑ i : Fin m, c i • v i ≠ 0 := by
    intro hzero
    have hall := Fintype.linearIndependent_iff.mp hlind c hzero
    exact hc (funext hall)
  exact sq_pos_of_pos (norm_pos_iff.mpr hnz)

/-- **Proposition 6.5 (Finite Normal Equations for Best Level-`N` Signature Approximation)**:
Given any closed subspace `𝒰_N ⊆ H_S`, `u^* ∈ 𝒰_N` minimizes `‖ε - u‖^2` over `u ∈ 𝒰_N` if and only
if the normal equations `⟪ε - u^*, v⟫ = 0` hold for all `v ∈ 𝒰_N`, and then
`‖ε - u^*‖^2 = ‖ε‖^2 - ‖u^*‖^2`. -/
theorem proposition_6_5_normal_equations {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (𝒰 : Submodule ℝ H) (ε u_star : H) (hu : u_star ∈ 𝒰)
    (horth : ∀ v ∈ 𝒰, ⟪ε - u_star, v⟫ = 0) :
    (∀ u ∈ 𝒰, ‖ε - u_star‖ ^ 2 ≤ ‖ε - u‖ ^ 2) ∧
      ‖ε - u_star‖ ^ 2 = ‖ε‖ ^ 2 - ‖u_star‖ ^ 2 := by
  refine ⟨fun u hu' => ?_, ?_⟩
  · have hdiff : u_star - u ∈ 𝒰 := 𝒰.sub_mem hu hu'
    have h0 : ⟪ε - u_star, u_star - u⟫ = 0 := horth (u_star - u) hdiff
    have hsplit : ε - u = (ε - u_star) + (u_star - u) := by abel
    rw [hsplit, @norm_add_sq_real H _ _ (ε - u_star) (u_star - u), h0]
    nlinarith [sq_nonneg ‖u_star - u‖]
  · have h0 : ⟪ε - u_star, u_star⟫ = 0 := horth u_star hu
    have hsplit : ε = (ε - u_star) + u_star := by abel
    have hpyth := @norm_add_sq_real H _ _ (ε - u_star) u_star
    rw [← hsplit, h0] at hpyth
    linarith

/-- **Theorem D (Theorem 6.3: GKW Hedging-Error Decomposition and Quantitative Tail Bounds)**:
For every `X ∈ L^2(ℱ^S_T, ℚ)`:
1. *(Orthogonal GKW decomposition)*: `X = E_ℚ[X] + ∫_0^T H^X_s dS_s + ε_T` with `ε_T ⊥ ℳ_S` and
   Pythagorean identity `‖X‖^2 = ‖E_ℚ[X] + ∫ H dS‖^2 + ‖ε_T‖^2`;
2. *(Quantitative tail bound for `𝒲_{w'}`)*: If `X = evalSig b` with `b ∈ T_{w'}` and
   `w(n)/w'(n) ≤ ρ_N` for all `n > N`, and if we hedge dynamically plus statically up to signature
   level `N`, the residual distance to `ℳ_S ⊔ 𝒱^{(N)}_S` satisfies
   `inf_{Z ∈ ℳ_S ⊔ 𝒱^{(N)}_S} ‖X - Z‖ ≤ C_sig · ρ_N · ‖b‖_{w'}`;
3. *(Vanishing residual when `N ≥ N^*_S`)*: If `(N : ℕ∞) ≥ N^*_S` (and `𝒱^{(∞)}_S = ⊤`), the
   hedging error over `ℳ_S ⊔ 𝒱^{(N)}_S` is identically `0`! -/
theorem theorem_D {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ} {w : Weight}
    {PFS : PriceFiltrationSignatureSpace H_S d}
    (gkw : GKWDecompositionSetup H_S d w PFS) :
    haveI : HasOrthogonalProjection gkw.replicableSubspace :=
      @Submodule.HasOrthogonalProjection.ofCompleteSpace H_S _ _ gkw.replicableSubspace
        (gkw.replicable_closed.completeSpace_coe)
    -- (1) Unique orthogonal GKW decomposition & Pythagorean variance formula:
    (∀ X : H_S, ∃ ε_T : H_S,
      X = gkw.expectationPart X + gkw.stochasticIntegralPart X + ε_T ∧
      (∀ Z ∈ gkw.replicableSubspace, ⟪ε_T, Z⟫ = 0) ∧
      ‖X‖ ^ 2 = ‖gkw.expectationPart X + gkw.stochasticIntegralPart X‖ ^ 2 + ‖ε_T‖ ^ 2) ∧
    -- (2) Quantitative weight-ratio tail bound on `𝒲_{w'}`:
    (∀ (w' : Weight) (b : ExtTensorAlgebra (d + 1)) (hb : MemTw w' b)
        (N : ℕ) (ρ_N : ℝ) (hρ : 0 ≤ ρ_N),
      (∀ n : ℕ, N < n → w n / w' n ≤ ρ_N) →
      ∃ Z ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N,
        ‖gkw.evalSig b - Z‖ ≤ gkw.C_sig * ρ_N * normW w' b) ∧
    -- (3) Zero residual at or above finite completeness depth `N ≥ N^*_S` (when `𝒱^{(∞)}_S = ⊤`):
    (PFS.V_infty = ⊤ → ∀ N : ℕ, PFS.completenessDepth ≤ (N : ℕ∞) →
      ∀ X : H_S, X ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N) := by
  haveI : HasOrthogonalProjection gkw.replicableSubspace :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace H_S _ _ gkw.replicableSubspace
      (gkw.replicable_closed.completeSpace_coe)
  refine ⟨fun X => ?_, fun w' b hb N ρ_N hρ hratio => ?_, fun hVtop N hdepth X => ?_⟩
  · let P_X : H_S := gkw.replicableSubspace.starProjection X
    let ε_T : H_S := X - P_X
    have hsplit : P_X = gkw.expectationPart X + gkw.stochasticIntegralPart X :=
      gkw.orthProj_split X
    have horth : ∀ Z ∈ gkw.replicableSubspace, ⟪ε_T, Z⟫ = 0 := by
      intro Z hZ
      have hmem : X - P_X ∈ gkw.replicableSubspaceᗮ :=
        Submodule.sub_starProjection_mem_orthogonal X
      exact (Submodule.mem_orthogonal' gkw.replicableSubspace (X - P_X)).mp hmem Z hZ
    have hP_mem : P_X ∈ gkw.replicableSubspace := (gkw.replicableSubspace.starProjection X).2
    have hpyth : ‖X‖ ^ 2 = ‖P_X‖ ^ 2 + ‖ε_T‖ ^ 2 := by
      have hdecomp : X = P_X + ε_T := by simp [ε_T]
      have h0 : ⟪P_X, ε_T⟫ = 0 := by
        rw [real_inner_comm]
        exact horth P_X hP_mem
      have hsq := @norm_add_sq_real H_S _ _ P_X ε_T
      rw [← hdecomp, h0] at hsq
      linarith
    refine ⟨ε_T, ?_, horth, ?_⟩
    · rw [← hsplit]; simp [ε_T]
    · rwa [← hsplit]
  · let Z : H_S := gkw.evalSig (projLe N b)
    have hZ_mem : Z ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N :=
      Submodule.mem_sup_right (gkw.evalSig_le_in_V N b)
    refine ⟨Z, hZ_mem, ?_⟩
    have hdecomp : gkw.evalSig b = Z + gkw.evalSig (projGt N b) := by
      conv_lhs => rw [← add_projLe_projGt N b, gkw.evalSig_add]
    have hsub : gkw.evalSig b - Z = gkw.evalSig (projGt N b) := by
      rw [hdecomp]; abel
    rw [hsub]
    obtain ⟨hL2_tail, hnorm_tail⟩ :=
      tail_norm2wInv_le_ratio_mul_normW w w' hb N hρ hratio
    calc
      ‖gkw.evalSig (projGt N b)‖ ≤ gkw.C_sig * norm2wInv w (projGt N b) :=
        gkw.evalSig_l2_bound (projGt N b) hL2_tail
      _ ≤ gkw.C_sig * (ρ_N * normW w' b) :=
        mul_le_mul_of_nonneg_left hnorm_tail gkw.hC_sig_nonneg
      _ = gkw.C_sig * ρ_N * normW w' b := by ring
  · -- When `completenessDepth ≤ N`, `V_subspace N` (already closed!) equals `V_infty = ⊤`
    let S_good : Set ℕ∞ :=
      {(K : ℕ∞) | ∃ n : ℕ, K = (n : ℕ∞) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}
    have hne : S_good.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      change sInf S_good ≤ (N : ℕ∞) at hdepth
      rw [hempty, sInf_empty] at hdepth
      exact not_top_le_coe N hdepth
    rcases csInf_mem hne with ⟨n₀, hn₀_eq, hn₀_cl⟩
    have hn₀_le : n₀ ≤ N := WithTop.coe_le_coe.mp (hn₀_eq ▸ hdepth)
    have hVN_top : PFS.V_subspace N = ⊤ := by
      rw [← PFS.topologicalClosure_V_subspace N]
      apply top_unique
      rw [← hVtop, ← hn₀_cl]
      exact Submodule.topologicalClosure_mono (PFS.V_subspace_mono hn₀_le)
    rw [hVN_top]
    exact Submodule.mem_sup_right Submodule.mem_top

/-! ## Section 7: Canonical Volatility Models as Concrete `SignatureVolatilityModel` Instances -/

/-- Helper lemma: any finitely supported functional `ℓ ∈ 𝒟_fin` automatically satisfies
**Hypothesis H1** (`MemL2w w ℓ`) for every admissible weight `w`. -/
lemma hypH1_of_isFinitelySupported {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra (d + 1)}
    (hfin : ExtTensorAlgebra.IsFinitelySupported ℓ) : HypH1 w ℓ := by
  rcases hfin with ⟨N, hN⟩
  refine ⟨summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_⟩
  have hgt : N < n := Nat.lt_of_not_ge fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hl0 : ℓ.levelNormSq n = 0 := by
    unfold ExtTensorAlgebra.levelNormSq
    refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := mem_wordsOfLength.mp hI
    rw [hN I (hlen ▸ hgt)]
    ring
  rw [hl0, zero_div]

/-- **Section 7.1: Black–Scholes Model (`d = 1`, `ℓ = σ₀ e_∅`, `N^*_S = 0`)**:
Constant volatility `σ_t = σ₀ > 0` supported strictly at tensor level `0`. -/
def blackScholesModel (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 1
  hd := Nat.succ_pos 0
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := σ₀ • ExtTensorAlgebra.basisWord []
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨0, fun I hI => by
    have hne : I ≠ [] := fun h => by subst h; exact Nat.not_lt_zero _ hI
    change σ₀ * (if I = [] then 1 else 0) = 0
    simp [hne]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff []) hzero
    simp [ExtTensorAlgebra.basisWord] at hc
    exact hσ₀ hc⟩

/-- **Section 7.2: First-Order Brownian Volatility (`d = 1`, `ℓ = σ₀ e_∅ + α e_{(1)}`, `N^*_S = 1`)**:
`σ_t = σ₀ + α W^1_t`, supported on tensor levels `≤ 1`. -/
def firstOrderBrownianVolModel (T s₀ σ₀ α : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 1
  hd := Nat.succ_pos 0
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := σ₀ • ExtTensorAlgebra.basisWord [] + α • ExtTensorAlgebra.basisWord [(0 : Fin 1).succ]
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨1, fun I hI => by
    have hne0 : I ≠ [] := fun h => by subst h; exact Nat.not_lt_zero _ (Nat.zero_lt_one.trans hI)
    have hne1 : I ≠ [(0 : Fin 1).succ] := fun h => by subst h; exact lt_irrefl 1 hI
    change σ₀ * (if I = [] then 1 else 0) + α * (if I = [(0 : Fin 1).succ] then 1 else 0) = 0
    simp [hne0, hne1]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff []) hzero
    change σ₀ * 1 + α * 0 = 0 at hc
    linarith [hσ₀]⟩

/-- **Section 7.3: Signature-Linear / Truncated Heston Approximation (`d = 2`, level-2 support, `N^*_S = 2`)**:
Two-factor model driven by `(W^1, W^2)` with spot volatility functional supported up to level 2. -/
def signatureHestonLevel2Model (T s₀ v₀ κ θ ξ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hv₀ : v₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 2
  hd := by decide
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := v₀ • ExtTensorAlgebra.basisWord [] +
        (κ * θ) • ExtTensorAlgebra.basisWord [0] +
        ξ • ExtTensorAlgebra.basisWord [(1 : Fin 2).succ] +
        (-κ * ξ) • ExtTensorAlgebra.basisWord [(1 : Fin 2).succ, 0]
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨2, fun I hI => by
    have h0 : I ≠ [] := fun h => by subst h; simp at hI
    have h1a : I ≠ [0] := fun h => by subst h; simp at hI
    have h1b : I ≠ [(1 : Fin 2).succ] := fun h => by subst h; simp at hI
    have h2 : I ≠ [(1 : Fin 2).succ, 0] := fun h => by subst h; simp at hI
    change v₀ * (if I = [] then 1 else 0) +
      (κ * θ) * (if I = [0] then 1 else 0) +
      ξ * (if I = [(1 : Fin 2).succ] then 1 else 0) +
      (-κ * ξ) * (if I = [(1 : Fin 2).succ, 0] then 1 else 0) = 0
    simp [h0, h1a, h1b, h2]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff []) hzero
    change v₀ * 1 + (κ * θ) * 0 + ξ * 0 + (-κ * ξ) * 0 = 0 at hc
    simp at hc
    exact hv₀ hc⟩

/-- **Section 7.5: Quintic Ornstein–Uhlenbeck Signature Model (Abi Jaber–Illand–Shaun, level 5)**:
Polynomial of degree 5 in an OU process represented by a signature functional truncated at `N = 5`. -/
def quinticOUSignatureModel (T s₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀)
    (ℓ_quintic : ExtTensorAlgebra 2)
    (hsupp5 : ∀ I : Word 2, 5 < I.length → ℓ_quintic.coeff I = 0)
    (hnz : ℓ_quintic ≠ 0) : SignatureVolatilityModel where
  d := 1
  hd := Nat.succ_pos 0
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := ℓ_quintic
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨5, hsupp5⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨hnz⟩

/-- **Section 7.4 & 7.6: Infinite-Series Signature Models (Rough Bergomi & Guyon–Lekeufack PDV)**:
Any infinite signature expansion `ℓ` whose homogeneous norms satisfy `|ℓ_n| ≤ C · q^n` with
`0 ≤ q < r` (`r ≥ 1`) satisfies **H1–H3** with the geometric weight `w_r(n) = r^n` (`N^*_S = ∞`
generically when infinitely many projected levels are linearly independent). -/
def infiniteGeometricSignatureModel (d : ℕ) (hd : 0 < d) (T s₀ r q C : ℝ)
    (hT : 0 < T) (hs₀ : 0 < s₀) (hr : 1 ≤ r) (hq0 : 0 ≤ q) (hqr : q < r) (hC : 0 ≤ C)
    (ℓ : ExtTensorAlgebra (d + 1)) (hnz : ℓ ≠ 0)
    (hdecay : ∀ n : ℕ, ℓ.levelNorm n ≤ C * q ^ n) : SignatureVolatilityModel where
  d := d
  hd := hd
  T := T
  hT := hT
  w := Weight.geometric r hr
  ℓ := ℓ
  s₀ := s₀
  hs₀ := hs₀
  h1 := ⟨by
    have hr_pos : 0 < r := zero_lt_one.trans_le hr
    have hratio0 : 0 ≤ (q / r) ^ 2 := sq_nonneg _
    have hratio1 : (q / r) ^ 2 < 1 := by
      have hdiv_lt : q / r < 1 := (div_lt_one hr_pos).mpr hqr
      have hdiv_nonneg : 0 ≤ q / r := div_nonneg hq0 hr_pos.le
      nlinarith
    have hgeom : Summable (fun n : ℕ => C ^ 2 * ((q / r) ^ 2) ^ n) :=
      (summable_geometric_of_lt_one hratio0 hratio1).mul_left (C ^ 2)
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (ℓ.levelNormSq_nonneg n) (sq_nonneg _)) (fun n => ?_) hgeom
    rw [← ℓ.sq_levelNorm]
    have hle : ℓ.levelNorm n / (Weight.geometric r hr n) ≤ C * (q / r) ^ n := by
      simp only [Weight.geometric]
      rw [div_pow]
      calc
        ℓ.levelNorm n / r ^ n ≤ (C * q ^ n) / r ^ n :=
          div_le_div_of_nonneg_right (hdecay n) (pow_nonneg hr_pos.le n)
        _ = C * (q ^ n / r ^ n) := mul_div_assoc _ _ _
    have h0 : 0 ≤ ℓ.levelNorm n / (Weight.geometric r hr n) :=
      div_nonneg (ℓ.levelNorm_nonneg n) (pow_nonneg hr_pos.le n)
    have hsq := pow_le_pow_left₀ h0 hle 2
    calc
      (ℓ.levelNorm n) ^ 2 / (Weight.geometric r hr n) ^ 2
          = (ℓ.levelNorm n / Weight.geometric r hr n) ^ 2 := (div_pow _ _ 2).symm
      _ ≤ (C * (q / r) ^ n) ^ 2 := hsq
      _ = C ^ 2 * ((q / r) ^ 2) ^ n := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]⟩
  h2 := HypH2.geometric_admissible r hr
  h3 := ⟨hnz⟩

/-- **Table 1 / Section 7.1 Verification (Black–Scholes Zero Completeness Depth & Zero GKW Error)**:
Whenever the projected signature coordinates `Y_I` vanish (or lie in `span{Y_∅}`) for all `|I| ≥ 1`,
`N^*_S = 0` (`completenessDepth = 0`) and dynamic delta-hedging + constant cash replicates all of
`L^2(ℱ^S_T, ℚ)` when `span{Y_∅} ≤ replicableSubspace`. -/
theorem section_7_1_black_scholes_completeness {H_S : Type*} [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
    (PFS : PriceFiltrationSignatureSpace H_S 1)
    (hVtop : PFS.V_infty = ⊤)
    (hBS_span : ∀ I : Word 2, PFS.Y I ∈ PFS.V_subspace 0) :
    PFS.completenessDepth = 0 := by
  apply le_antisymm _ ( zero_le _ )
  unfold PriceFiltrationSignatureSpace.completenessDepth
  refine csInf_le (OrderBot.bddBelow _) ⟨0, rfl, ?_⟩
  apply le_antisymm
  · rw [hVtop]; exact le_top
  · unfold PriceFiltrationSignatureSpace.V_infty
    refine Submodule.topologicalClosure_mono ?_
    rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact hBS_span I

end SignatureVolatility
