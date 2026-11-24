module

public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.SignatureVolatilityModel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-!
# Shared definition of Carbon's function `v₁`

`counterexampleV1 B hd s x` is the expectation
`E[exp(⅓((x+B_s)³-x³) - ∫₀ˢ(x+B_r) dr - ½∫₀ˢ(x+B_r)⁴ dr)]`
against the first coordinate of `B`. The Pillar B lemmas B1–B5 are
properties of `counterexampleV1AtHalf M B`, the specialisation at
horizon `M.T / 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The exponent in Carbon's `v_1(s, x)` along a single path. -/
def counterexampleV1Exponent {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (s x : ℝ) (ω : Ω) : ℝ :=
  let Wr : ℝ → ℝ := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
  (1 / 3 : ℝ) * ((x + Wr s) ^ 3 - x ^ 3)
    - (∫ r in (0 : ℝ)..s, x + Wr r)
    - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s, (x + Wr r) ^ 4)

/-- Carbon's `v_1(s, x)`. -/
def counterexampleV1 {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (s x : ℝ) : ℝ :=
  ∫ ω, Real.exp (counterexampleV1Exponent B hd s x ω) ∂P

/-- The function `v₁` used in Pillar B, at horizon `M.T / 2`. -/
def counterexampleV1AtHalf (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (x : ℝ) : ℝ :=
  counterexampleV1 B M.hd (M.T / 2) x

end SignatureVolatility
