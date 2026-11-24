module

public import SignatureVolatility.SignatureRiccatiKit.CondSigPoly
public import SignatureVolatility.SignatureRiccatiKit.ItoWordTiltClosedForm
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds

/-!
# C2c. Identification of `paperSig2` with `condSigPoly` under the complex tilt
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Every word `I` matches `condSigPoly` under the tilted complex exponential. -/
lemma integral_paperSig2_eq_condSigPoly {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (I : Word (d + 1)) (ξ : ℝ) :
    ∫ ω, ((paperSig2 B 0 t ω).coeff I : ℂ) * complexTilt B hd ξ t ω ∂P =
      ∫ ω, condSigPoly hd t I (MultiBrownian.W B t ω ⟨0, hd⟩) *
        complexTilt B hd ξ t ω ∂P := by
  sorry

end SignatureVolatility
