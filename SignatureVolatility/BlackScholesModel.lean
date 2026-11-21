import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.HypH2
import SignatureVolatility.Weight.ConstOne
import SignatureVolatility.ExtTensorAlgebra.BasisWord
import SignatureVolatility.HypH1OfIsFinitelySupported


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
