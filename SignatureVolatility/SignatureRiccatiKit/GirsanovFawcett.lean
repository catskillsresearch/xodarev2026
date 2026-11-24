module

public import SignatureVolatility.SignatureRiccatiKit.FawcettHermite
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.WordsOfLength


/-!
# C2. Girsanov–Fawcett identification

Identifies each signature coordinate `Ŵ_t^I` with Carbon's word polynomial
`P_{I,t}` evaluated at the first Brownian coordinate `W_t^0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **C2.** For every word `I` and every `t ∈ (0, T]`, the signature coordinate
`Ŵ_t^I` agrees almost surely with `P_{I,t}(W_t^0)`. -/
lemma girsanov_fawcett_identification {d : ℕ} (hd : 0 < d)
    (B : MultiBrownian Ω P d) {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t ≤ T)
    (I : Word (d + 1)) :
    (fun ω => ((paperSetup B hT).W_hat t ω).coeff I) =ᵐ[P]
      fun ω => (fawcettPoly hd I t (MultiBrownian.W B t ω ⟨0, hd⟩)).re := by
  sorry

end SignatureVolatility
