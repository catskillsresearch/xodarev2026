module

public import SignatureVolatility.SignatureRiccatiKit.ComplexTilt
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics

/-!
# C2. Closed form for the tilted expectation of every Itô word integral
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Exact closed form for `𝔼[itoWordIntegral B 0 t J · E_t(ξ)]`.
No Girsanov and no product Itô rule: induction on `J` via
`ae_itoWordIntegral_time_cons` and uniform Riemann sums. -/
theorem integral_itoWordIntegral_mul_complexTilt {d : ℕ}
    (B : MultiBrownian Ω P d) (hd : 0 < d) (ξ : ℝ) (J : Word (d + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (itoWordIntegral B 0 t ω J : ℂ) * complexTilt B hd ξ t ω ∂P =
      if onlyZeroOrOne hd J then
        (Complex.I * (ξ : ℂ)) ^ (countOnes hd J) *
          ((t ^ J.length / (J.length.factorial : ℝ) : ℝ) : ℂ)
      else 0 := by
  sorry

end SignatureVolatility
