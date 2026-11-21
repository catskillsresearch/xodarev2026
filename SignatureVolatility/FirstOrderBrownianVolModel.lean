module

public import SignatureVolatility.ExtTensorAlgebra.BasisWord
public import SignatureVolatility.HypH1OfIsFinitelySupported
public import SignatureVolatility.HypH2
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.Weight.ConstOne


@[expose] public section

noncomputable section

namespace SignatureVolatility

private def firstOrderWord : Word 2 := [1]

def firstOrderBrownianVolModel (T s₀ σ₀ α : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 1
  hd := Nat.succ_pos 0
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := σ₀ • ExtTensorAlgebra.basisWord ([] : Word 2) +
      α • ExtTensorAlgebra.basisWord firstOrderWord
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨1, fun I hI => by
    have hne0 : I ≠ [] := fun h => by subst h; simp at hI
    have hne1 : I ≠ firstOrderWord := fun h => by subst h; simp [firstOrderWord] at hI
    change σ₀ * (if I = [] then 1 else 0) + α * (if I = firstOrderWord then 1 else 0) = 0
    simp [hne0, hne1]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff ([] : Word 2)) hzero
    rw [show (0 : ExtTensorAlgebra 2).coeff ([] : Word 2) = 0 from rfl] at hc
    have hc' : σ₀ * 1 + α * 0 = 0 := by
      conv_lhs at hc => simp [ExtTensorAlgebra.basisWord, firstOrderWord]
      exact hc
    simpa using hσ₀ (by linarith)⟩

end SignatureVolatility
