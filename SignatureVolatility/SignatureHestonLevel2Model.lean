import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.HypH2
import SignatureVolatility.Weight.ConstOne
import SignatureVolatility.ExtTensorAlgebra.BasisWord
import SignatureVolatility.HypH1OfIsFinitelySupported


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
