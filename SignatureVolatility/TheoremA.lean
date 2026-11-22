module

public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.TheoremAOfBrownianSetupItoKit


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem A.** Existence/uniqueness of the signature-price solution over Brownian motion
(Stratonovich prolonged setup + MathFin Ito kit). Uniqueness is among strong solutions: adapted to
the signature filtration and in `KitStrongSolutionClass` (square-integrable supremum, `L⁴`-regular
integrand), which the constructed Doléans solution satisfies. -/
theorem theorem_A (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT),
      ∀ S_tilde : ℝ → Ω → ℝ,
        (∀ t ∈ Icc 0 M.T, Measurable[(paperSetup B M.hT).signatureFiltration.σAlg t] (S_tilde t)) →
        KitStrongSolutionClass P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))
          S_tilde →
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P,
          S_tilde t ω = M.s₀ + (itoCalculusKit_of_mathfin B M.hT).itoInt
            (fun s ω' => S_tilde s ω' *
              SignatureVolatilityModel.sigma M (paperSetup B M.hT) s ω')
            t ω) →
        ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P, S_tilde t ω = sol.S t ω :=
  theorem_A_of_Brownian_Setup_Ito_Kit M (paperSetup B M.hT)
    (itoCalculusKit_of_mathfin B M.hT) h3
    (ae_of_all P fun ω => continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1 ω)

end SignatureVolatility
