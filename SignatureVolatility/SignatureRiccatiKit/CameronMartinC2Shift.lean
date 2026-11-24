module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# B3a. Deterministic Cameron–Martin shift for a C² path with `h(0) = 0`
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Pathwise Doléans exponent along an arbitrary continuous path. -/
noncomputable def pathExponent (w : ℝ → ℝ) (x s : ℝ) : ℝ :=
  (1 / 3 : ℝ) * ((x + w s) ^ 3 - x ^ 3)
    - (∫ r in (0 : ℝ)..s, x + w r)
    - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s, (x + w r) ^ 4)

/-- If `h` is `C²` on `[0, s₀]` with `h 0 = 0`, and `Ψ` is the pathwise
combination of the shifted exponent with the Cameron–Martin weight, then
`∫ exp(Φ(x,s₀)) = ∫ exp(Ψ)`. -/
lemma cameronMartin_C2_shift {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (h : ℝ → ℝ) (x : ℝ) (Ψ : Ω → ℝ)
    (hh0 : h 0 = 0)
    (hdiff : ContDiffOn ℝ 2 h (Set.Icc 0 s₀))
    (hpath : ∀ ω,
      let w := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
      pathExponent (fun r => w r + h r) x s₀
        - deriv h s₀ * w s₀
        + (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)
        - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2)
      = Ψ ω) :
    ∫ ω, Real.exp (counterexampleV1Exponent B hd s₀ x ω) ∂P =
      ∫ ω, Real.exp (Ψ ω) ∂P := by
  sorry

end SignatureVolatility
