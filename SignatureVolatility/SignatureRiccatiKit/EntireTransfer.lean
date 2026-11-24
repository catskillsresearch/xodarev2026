module

public import SignatureVolatility.SignatureRiccatiKit.FawcettHermite
public import SignatureVolatility.SignatureRiccatiKit.FawcettEntireBound
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.MemTw
public import SignatureVolatility.DualPairing
public import SignatureVolatility.SignatureVolatilityModel
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


/-!
# C3. Transfer from the Fawcett expansion to `f`

Given `⟨φ, Ŵ_t⟩ = f(W_t^0)` a.s. and the Girsanov–Fawcett identification,
`f` agrees Lebesgue-a.e. with an entire function of exponential type `≤ 1`.
This is the last step of Pillar C.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **C3.** Transfer of the word-polynomial expansion to a measurable `f` with
`⟨φ, Ŵ_t⟩ = f(W_t^0)` a.s. The conclusion is exactly that of Pillar C. -/
lemma fawcett_transfer_to_f (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ M.T)
    {phi : ExtTensorAlgebra (M.d + 1)} (hphi : MemTw M.w phi) {f : ℝ → ℝ}
    (hfeq : (fun ω => dualPairing phi ((paperSetup B M.hT).W_hat t ω)) =ᵐ[P]
      fun ω => f (MultiBrownian.W B t ω ⟨0, M.hd⟩))
    (hident : ∀ I : Word (M.d + 1),
      (fun ω => ((paperSetup B M.hT).W_hat t ω).coeff I) =ᵐ[P]
        fun ω => (fawcettPoly M.hd I t (MultiBrownian.W B t ω ⟨0, M.hd⟩)).re) :
    ∃ (G : ℂ → ℂ) (C : ℝ), Differentiable ℂ G ∧ 0 ≤ C ∧
      (∀ z : ℂ, ‖G z‖ ≤ C * Real.exp ‖z‖) ∧
      (∀ᵐ x : ℝ ∂volume, G x = (f x : ℂ)) := by
  sorry

end SignatureVolatility
