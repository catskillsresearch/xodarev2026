import Mathlib
import SignatureVolatility.Word
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

open Set

namespace SignatureVolatility

/-- Price-filtration signature space for completeness / GKW analysis. -/
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
    (Submodule.topologicalClosure
      (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S) = ⊤) ∧
    (∀ N : ℕ,
      Submodule.topologicalClosure
        (dynamicGainSubspace ⊔
          Submodule.span ℝ ((callPayoff '' 𝒦) ∪ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)}) :
          Submodule ℝ H_S) = ⊤ ↔
      Submodule.topologicalClosure
        (Submodule.span ℝ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)} : Submodule ℝ H_S) =
        Submodule.topologicalClosure (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S))

end SignatureVolatility