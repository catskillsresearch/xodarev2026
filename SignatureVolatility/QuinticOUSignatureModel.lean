module

public import SignatureVolatility.HypH1OfIsFinitelySupported
public import SignatureVolatility.HypH2
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.Weight.ConstOne
public import SignatureVolatility.Word


@[expose] public section

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
