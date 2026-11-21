import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.HypH2
import SignatureVolatility.Weight.ConstOne
import SignatureVolatility.ExtTensorAlgebra.BasisWord
import SignatureVolatility.HypH1OfIsFinitelySupported


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
