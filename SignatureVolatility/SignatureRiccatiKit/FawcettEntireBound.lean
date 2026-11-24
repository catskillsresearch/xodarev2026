module

public import SignatureVolatility.SignatureRiccatiKit.FawcettHermite
public import SignatureVolatility.MemTw
public import Mathlib.Data.Nat.Choose.Multinomial


/-!
# C1b. Counting identity, polynomial bound, and entire type `≤ 1`

These are the remaining combinatorial / entire-function facts from Carbon's
Step 5, not yet proved in `FawcettHermite`. They are needed by C3 (the
transfer to `f`). The Girsanov–Fawcett identification itself is C2.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory
open scoped Nat

namespace SignatureVolatility

/-- Number of functions `Fin (∑ c) → α` with prescribed fibre sizes equals
the multinomial coefficient. -/
lemma card_fun_eq_multinomial {α : Type*} [DecidableEq α] [Fintype α] (c : α → ℕ) :
    ((Finset.univ : Finset (Fin (∑ x : α, c x) → α)).filter
        (fun f => ∀ x, (Finset.univ.filter (fun i => f i = x)).card = c x)).card =
      Nat.multinomial (Finset.univ : Finset α) c := by
  sorry

/-- Carbon's counting identity:
`∑_{|I|=n} c(I; a, k, b) = (a+k+∑b)! / (a! k! ∏ b_j!)` if `n = a+k+2∑b`,
and `0` otherwise. -/
lemma sum_parseCount (d : ℕ) (hd : 0 < d) (n a k : ℕ) (b : Fin d → ℕ) :
    ∑ I ∈ wordsOfLength (d + 1) n, parseCount d hd I a k b =
      if n = a + k + 2 * ∑ j, b j then
        Nat.multinomial Finset.univ (blockCount d a k b)
      else 0 := by
  sorry

/-- Carbon's bound:
`∑_I ‖P_{I,t}(z)‖ ≤ 2 exp(t + (d+1)t/2) e^{‖z‖}`. -/
lemma sum_norm_fawcettPoly_le {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ∑' n : ℕ, ∑ I ∈ wordsOfLength (d + 1) n, ‖fawcettPoly hd I t z‖ ≤
      2 * Real.exp (t + (d + 1) * t / 2) * Real.exp ‖z‖ := by
  sorry

/-- For `φ ∈ T_w` and `t ≥ 0`, `G(z) = ∑_I φ_I P_{I,t}(z)` is entire of
exponential type `≤ 1`. -/
lemma fawcettEntire_expTypeOne {d : ℕ} (hd : 0 < d)
    {w : Weight} {phi : ExtTensorAlgebra (d + 1)} (hphi : MemTw w phi)
    {t : ℝ} (ht : 0 ≤ t) :
    Differentiable ℂ (fawcettEntire hd phi t) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : ℂ, ‖fawcettEntire hd phi t z‖ ≤ C * Real.exp ‖z‖ := by
  sorry

end SignatureVolatility
