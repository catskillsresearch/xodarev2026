module

public import SignatureVolatility.ProlongedBrownianSetup.ShiftedWordIntegral

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace SignatureVolatility

/-!
# Chen and shuffle identities for the paper signature `Ŵ`

Chen is proved first for the Itô word integrals, by induction on the word. The step uses the
restart identity of `ShiftedWordIntegral` and the additivity of the Itô integral in its upper
limit. It is then carried to the Stratonovich coordinates, because the contraction expansion
`stratWordIntegral_eq_list` is compatible with deconcatenation.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Chen's identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_chen (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B 0 t ω = paperSig2 B 0 s ω ⊗ₜ paperSig2 B s t ω := by
  sorry

/-- **Shuffle identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_shuffle (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (I J : Word (d + 1)) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff I * (paperSig2 B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (paperSig2 B 0 t ω) := by
  sorry

end SignatureVolatility
