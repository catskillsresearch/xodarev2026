module

public import SignatureVolatility.ExtTensorAlgebra.TensorExpShuffle
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian

@[expose] public section

open MeasureTheory List

noncomputable section

namespace SignatureVolatility

open ExtTensorAlgebra

/-!
# Dyadic geometric approximants of the prolonged Brownian signature

Piecewise-linear signatures along the uniform dyadic mesh of `[s, t]`: each step is a
`tensorExp` of the prolonged increment, folded with `⊗ₜ`.

At every finite resolution the approximants are multiplicative (`foldTensorExp_append`) and
group-like (`foldTensorExp_shuffle`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Prolonged increment `wAug b − wAug a` on `[a, b]`. -/
def wAugIncr (B : MultiBrownian Ω P d) (a b : ℝ) (ω : Ω) : Fin (d + 1) → ℝ :=
  fun j => MultiBrownian.wAug B b ω j - MultiBrownian.wAug B a ω j

lemma wAugIncr_time (B : MultiBrownian Ω P d) (a b : ℝ) (ω : Ω) :
    wAugIncr B a b ω ⟨0, Nat.succ_pos _⟩ = b - a := by
  simp [wAugIncr, MultiBrownian.wAug]

lemma wAugIncr_space (B : MultiBrownian Ω P d) (a b : ℝ) (ω : Ω) (i : Fin d) :
    wAugIncr B a b ω ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩ =
      MultiBrownian.W B b ω i - MultiBrownian.W B a ω i := by
  simp [wAugIncr, MultiBrownian.wAug]

lemma measurable_wAugIncr (B : MultiBrownian Ω P d) (a b : ℝ) (j : Fin (d + 1)) :
    Measurable (fun ω => wAugIncr B a b ω j) :=
  (MultiBrownian.wAug_meas B b j).sub (MultiBrownian.wAug_meas B a j)

/-- Consecutive differences of a real sequence. -/
def consecutiveDiffs (pts : List ℝ) (f : ℝ → ℝ) : List ℝ :=
  (zip pts pts.tail).map fun p => f p.2 - f p.1

lemma sum_consecutiveDiffs : ∀ (pts : List ℝ) (f : ℝ → ℝ) (hs : pts ≠ []),
    (consecutiveDiffs pts f).sum = f (pts.getLast hs) - f (pts.head hs)
  | [], _, hs => (hs rfl).elim
  | [a], f, _ => by simp [consecutiveDiffs]
  | a :: b :: pts, f, _ => by
    have hs' : b :: pts ≠ [] := cons_ne_nil _ _
    have ih := sum_consecutiveDiffs (b :: pts) f hs'
    simp only [consecutiveDiffs, tail_cons, zip_cons_cons, map_cons, sum_cons, head_cons,
      getLast_cons (cons_ne_nil _ _)] at ih ⊢
    rw [ih]
    ring

/-- Left endpoints of the uniform partition of `[s, t]` into `n + 1` steps, then `t`.
Empty when `¬ s ≤ t`. -/
def dyadicPartition (s t : ℝ) (n : ℕ) : List ℝ :=
  if _h : s ≤ t then
    (range (n + 1)).map (fun k : ℕ => s + (t - s) * (k : ℝ) / (n + 1 : ℝ)) ++ [t]
  else
    []

lemma dyadicPartition_of_le {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    dyadicPartition s t n =
      (range (n + 1)).map (fun k : ℕ => s + (t - s) * (k : ℝ) / (n + 1 : ℝ)) ++ [t] := by
  simp [dyadicPartition, hst]

lemma dyadicPartition_ne_nil {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    dyadicPartition s t n ≠ [] := by
  simp [dyadicPartition_of_le hst]

lemma dyadicPartition_zero {s t : ℝ} (hst : s ≤ t) :
    dyadicPartition s t 0 = [s, t] := by
  simp [dyadicPartition_of_le hst]

/-- Consecutive prolonged increments along `dyadicPartition s t n`. -/
def dyadicIncrements (B : MultiBrownian Ω P d) (s t : ℝ) (n : ℕ) (ω : Ω) :
    List (Fin (d + 1) → ℝ) :=
  if _hst : s ≤ t then
    let pts := dyadicPartition s t n
    (zip pts pts.tail).map fun p => wAugIncr B p.1 p.2 ω
  else
    []

/-- Dyadic geometric signature approximant. -/
def sig2StratDyadic (B : MultiBrownian Ω P d) (s t : ℝ) (n : ℕ) (ω : Ω) :
    ExtTensorAlgebra (d + 1) :=
  foldTensorExp (dyadicIncrements B s t n ω)

lemma dyadicIncrements_of_le (B : MultiBrownian Ω P d) {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    (ω : Ω) :
    dyadicIncrements B s t n ω =
      (zip (dyadicPartition s t n) (dyadicPartition s t n).tail).map
        fun p => wAugIncr B p.1 p.2 ω := by
  simp [dyadicIncrements, hst]

lemma dyadicIncrements_zero (B : MultiBrownian Ω P d) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    dyadicIncrements B s t 0 ω = [wAugIncr B s t ω] := by
  simp [dyadicIncrements_of_le B hst, dyadicPartition_zero hst]

lemma sig2StratDyadic_zero (B : MultiBrownian Ω P d) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    sig2StratDyadic B s t 0 ω = tensorExp (wAugIncr B s t ω) := by
  rw [sig2StratDyadic, dyadicIncrements_zero B hst, foldTensorExp]
  exact concat_tensorExp_zero_right _

/-- Split mesh: dyadic increments on `[r, s]` followed by those on `[s, t]`. -/
def dyadicIncrementsSplit (B : MultiBrownian Ω P d) (r s t : ℝ) (n : ℕ) (ω : Ω) :
    List (Fin (d + 1) → ℝ) :=
  dyadicIncrements B r s n ω ++ dyadicIncrements B s t n ω

/-- Chen identity for split-mesh dyadic approximants at each finite `n`. -/
lemma sig2StratDyadic_chen_split (B : MultiBrownian Ω P d) (r s t : ℝ) (n : ℕ) (ω : Ω) :
    foldTensorExp (dyadicIncrementsSplit B r s t n ω) =
      sig2StratDyadic B r s n ω ⊗ₜ sig2StratDyadic B s t n ω := by
  simpa [dyadicIncrementsSplit, sig2StratDyadic] using
    foldTensorExp_append (dyadicIncrements B r s n ω) (dyadicIncrements B s t n ω)

lemma dyadicPartition_head {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    (dyadicPartition s t n).head (dyadicPartition_ne_nil hst n) = s := by
  simp [dyadicPartition_of_le hst, range_succ_eq_map]

lemma dyadicPartition_getLast {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    (dyadicPartition s t n).getLast (dyadicPartition_ne_nil hst n) = t := by
  simp [dyadicPartition_of_le hst]

/-- Level-1 coefficients of the dyadic approximant are exact increments (any `n`). -/
lemma sig2StratDyadic_coeff_singleton (B : MultiBrownian Ω P d) {s t : ℝ} (hst : s ≤ t)
    (n : ℕ) (ω : Ω) (j : Fin (d + 1)) :
    (sig2StratDyadic B s t n ω).coeff [j] = wAugIncr B s t ω j := by
  have hpts := dyadicPartition_ne_nil hst n
  have hmap :
      ((dyadicIncrements B s t n ω).map (fun v => v j)).sum =
        (consecutiveDiffs (dyadicPartition s t n)
          (fun u => MultiBrownian.wAug B u ω j)).sum := by
    simp only [dyadicIncrements_of_le B hst, consecutiveDiffs, map_map]
    rfl
  have htel := sum_consecutiveDiffs (dyadicPartition s t n)
    (fun u => MultiBrownian.wAug B u ω j) hpts
  rw [sig2StratDyadic, foldTensorExp_level1_sum, hmap, htel,
    dyadicPartition_head hst n, dyadicPartition_getLast hst n, wAugIncr]

lemma sig2StratDyadic_coeff_nil (B : MultiBrownian Ω P d) (s t : ℝ) (n : ℕ) (ω : Ω) :
    (sig2StratDyadic B s t n ω).coeff [] = 1 :=
  foldTensorExp_coeff_nil _

/-- Shuffle identity for dyadic approximants (group-like at each finite `n`). -/
lemma sig2StratDyadic_shuffle (B : MultiBrownian Ω P d) (s t : ℝ) (n : ℕ) (ω : Ω)
    (I J : Word (d + 1)) :
    (sig2StratDyadic B s t n ω).coeff I * (sig2StratDyadic B s t n ω).coeff J =
      evalShuffleBasis I J (sig2StratDyadic B s t n ω) :=
  foldTensorExp_shuffle _ I J

end SignatureVolatility
