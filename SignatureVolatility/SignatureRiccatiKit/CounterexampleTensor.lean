module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported


/-!
# Counterexample tensor family `u₀^(λ)`

Shared algebraic data for the affine / Riccati duality counterexample: the first
space letter and the finitely supported family
`u₀^(λ) = 2λ e_{[1,1,1]} − λ e_{[1,0]} − 12λ² e_{[1,1,1,1,0]}`.
-/

@[expose] public section

namespace SignatureVolatility

open ExtTensorAlgebra

/-- First spatial letter `1 = (0 : Fin d).succ` when `0 < d`. -/
def firstSpace {d : ℕ} (hd : 0 < d) : Letter (d + 1) :=
  (⟨0, hd⟩ : Fin d).succ

lemma firstSpace_ne_zero {d : ℕ} (hd : 0 < d) : firstSpace hd ≠ 0 :=
  Fin.succ_ne_zero _

/-- Counterexample tensor family `u₀^(λ) = 2λ e_{[1,1,1]} - λ e_{[1,0]} - 12λ² e_{[1,1,1,1,0]}`. -/
def counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I =>
    if I = [firstSpace hd, firstSpace hd, firstSpace hd] then 2 * lam
    else if I = [firstSpace hd, 0] then -lam
    else if I = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] then
      -12 * lam ^ 2
    else 0⟩

lemma counterexampleU0_coeff {d : ℕ} (hd : 0 < d) (lam : ℝ) (I : Word (d + 1)) :
    (counterexampleU0 hd lam).coeff I =
      if I = [firstSpace hd, firstSpace hd, firstSpace hd] then 2 * lam
      else if I = [firstSpace hd, 0] then -lam
      else if I = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] then
        -12 * lam ^ 2
      else 0 :=
  rfl

lemma counterexampleU0_coeff_zero {d : ℕ} (hd : 0 < d) (lam : ℝ) {I : Word (d + 1)}
    (h3 : I ≠ [firstSpace hd, firstSpace hd, firstSpace hd])
    (h2 : I ≠ [firstSpace hd, 0])
    (h5 : I ≠ [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0]) :
    (counterexampleU0 hd lam).coeff I = 0 := by
  simp [counterexampleU0_coeff, h3, h2, h5]

lemma counterexampleU0_isFinitelySupported {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    IsFinitelySupported (counterexampleU0 hd lam) := by
  refine ⟨5, fun I hI => ?_⟩
  simp only [counterexampleU0]
  split_ifs with h1 h2 h3
  · subst h1; simp at hI
  · subst h2; simp at hI
  · subst h3; simp at hI
  · rfl

end SignatureVolatility
