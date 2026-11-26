module

public import SignatureVolatility.TheoremBOfSetupItoRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.CoordSemimartingale
public import SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp
public import SignatureVolatility.SigPriceCont


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper Theorem B, `→` part (proved)

Paper Theorem B: under H1–H3 the Theorem A price is a martingale on the signature filtration,
Delbaen–Schachermayer NFLVR holds for admissible strategies whose wealth is uniformly bounded
from below, every signature coordinate is a special semimartingale, and (part (ii)) the
conditional transform of every finitely supported `u₀` with finite signature transform is
exponential-affine iff the Riccati equation `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, has a global classical
solution.

`theorem_B_mp` proves everything except the `←` direction of (ii): the martingale,
Delbaen–Schachermayer NFLVR for a continuous version of the packaged price, special-semimartingale
conclusions, and the `→` direction of the Riccati equivalence (`affine_riccati_duality_mp`).
The `←` direction and the full paper conjunction are false as universal statements; their
negations are `not_theorem_B_mpr` and `not_theorem_B`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B, `→` part (proved).** Martingale property on the signature filtration,
Delbaen–Schachermayer NFLVR for uniformly bounded-below admissible gains of a continuous
version of the packaged price, special-semimartingale signature coordinates (Lemma 43), and
the `→` direction of the Riccati transform equivalence (Theorem 4.2(ii)): an exponential-affine
conditional transform through a classical Riccati solution yields a global classical Riccati
solution. -/
theorem theorem_B_mp (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ (sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT)),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) P ∧
        P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
      SatisfiesNFLVR_DS P
        (BoundedBelowGains (paperSetup B M.hT).signatureFiltration.σAlg P
          (fun t ω => MultiBrownian.W B t ω (kitDriver M.hd))
          (sigPriceCont M B)
          (SignatureVolatilityModel.sigma M (paperSetup B M.hT)) M.T) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale P
          (paperSetup B M.hT).signatureFiltration M.T
          (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
        (∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1
              ((paperSetup B M.hT).W_hat M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1
                ((paperSetup B M.hT).W_hat M.T ω)) |
              (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t))
                ((paperSetup B M.hT).W_hat t ω))) →
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) := by
  obtain ⟨sol, _⟩ := theorem_A_of_Brownian_Setup_Ito_Kit M (paperSetup B M.hT)
    (itoCalculusKit_of_mathfin B M.hT) h3
    (ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1)
  exact ⟨sol, sol.is_martingale, satisfiesNFLVR_DS_sigPriceCont M B h3,
    fun I => ⟨isSpecialSemimartingale_paperSig2_coeff B I M.hT⟩,
    fun u₀ hf h => affine_riccati_duality_mp M B u₀ hf h⟩

end SignatureVolatility
