module

public import SignatureVolatility.SignatureRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.RiccatiOp
public import SignatureVolatility.ItoCalculusKit.OfMathFin


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Affine / Riccati duality: the proved direction

Paper Theorem 4.2(ii) (p. 21) states, for finitely supported `u₀` with finite signature
transform, that the conditional transform is exponential-affine,
`𝔼[exp⟨u₀, Ŵ_T⟩ | ℱ_t] = exp⟨ψ(T − t), Ŵ_t⟩` for a classical solution `ψ` of `∂ψ = ℛ(ψ)`,
`ψ(0) = u₀`, **iff** a global classical Riccati solution exists.

This file records the immediate implication (`affine_riccati_duality_mp`): a classical
Riccati solution satisfying the exponential dual formula yields a classical Riccati
solution. The premise already supplies that solution, so the implication is not a
substantive forward pricing result. The `←` direction (that a classical Riccati solution
implies the exponential dual-pricing formula) is false as a universal statement; see
`not_affine_riccati_duality_mpr`.

Proved supporting fact for `←` (in `RiccatiExpProcess`): along a classical solution the exponent
`⟨ψ(T − t), Ŵ_t⟩` is a.s. summable and continuous in `t`
(`ClassicalRiccatiSolution.ae_exponent_summable_continuousOn`). The positive local martingale
property itself needs a multi-driver exponential Itô formula with random integrands, which the
library does not yet have.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Affine / Riccati duality, recorded implication** (paper Theorem 4.2(ii), p. 21). A
classical Riccati solution of `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, that satisfies the exponential dual
formula yields a classical Riccati solution. Immediate (the premise already supplies the
solution); not a substantive forward pricing result. -/
theorem affine_riccati_duality_mp (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)) :
    SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
    (∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
        P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω))) →
    Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) :=
  fun _ ⟨sol, _⟩ => ⟨sol⟩

end SignatureVolatility
