import SignatureVolatility.ExtTensorAlgebra.BasisWord
import SignatureVolatility.HypH1OfIsFinitelySupported
import SignatureVolatility.HypH2
import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.Weight.ConstOne
import SignatureVolatility.Word

noncomputable section

namespace SignatureVolatility

private def hestonL0 : Word 3 := [0]
private def hestonL1 : Word 3 := [2]
private def hestonL2 : Word 3 := [2, 0]

def signatureHestonLevel2Model (T s₀ v₀ κ θ ξ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hv₀ : v₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 2
  hd := by decide
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := v₀ • ExtTensorAlgebra.basisWord ([] : Word 3) +
      (κ * θ) • ExtTensorAlgebra.basisWord hestonL0 +
      ξ • ExtTensorAlgebra.basisWord hestonL1 +
      (-κ * ξ) • ExtTensorAlgebra.basisWord hestonL2
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨2, fun I hI => by
    have h0 : I ≠ [] := fun h => by subst h; simp at hI
    have h1a : I ≠ hestonL0 := fun h => by subst h; simp [hestonL0] at hI
    have h1b : I ≠ hestonL1 := fun h => by subst h; simp [hestonL1] at hI
    have h2 : I ≠ hestonL2 := fun h => by subst h; simp [hestonL2] at hI
    change v₀ * (if I = [] then 1 else 0) +
      (κ * θ) * (if I = hestonL0 then 1 else 0) +
      ξ * (if I = hestonL1 then 1 else 0) +
      (-κ * ξ) * (if I = hestonL2 then 1 else 0) = 0
    simp [h0, h1a, h1b, h2]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff ([] : Word 3)) hzero
    rw [show (0 : ExtTensorAlgebra 3).coeff [] = 0 from rfl] at hc
    change (v₀ * (if ([] : Word 3) = [] then (1 : ℝ) else 0) +
        (κ * θ) * (if ([] : Word 3) = hestonL0 then 1 else 0) +
        ξ * (if ([] : Word 3) = hestonL1 then 1 else 0) +
        (-κ * ξ) * (if ([] : Word 3) = hestonL2 then 1 else 0)) = 0 at hc
    simp [hestonL0, hestonL1, hestonL2] at hc
    exact hv₀ hc⟩

end SignatureVolatility