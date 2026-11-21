module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Paper-strength Stratonovich / Itô signature of `(t, W)` (Phase 1)

The chordal lift in `SignatureOfBM` is a stand-in. The paper uses the true Stratonovich
(equivalently Itô + half-Laplacian) iterated-integral signature of the time-augmented path.

**Status: HOLE.** Downstream paper theorems A–D are wired to this constructor.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Paper goal.** `ProlongedBrownianSetup` whose `sig2` is the Stratonovich/Itô signature of
`(t, W_t)`, discharging Chen, shuffle, adaptedness, and Appendix A factorial moments. -/
noncomputable def prolongedBrownianSetup_stratonovich_of_brownian {T : ℝ}
    (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ProlongedBrownianSetup Ω P d T := by
  -- Recursive MathFin Itô/Stratonovich iterated integrals into ExtTensorAlgebra;
  -- discharge sig2_empty/time/space, Chen, shuffle, factorial_moment_control.
  sorry

end SignatureVolatility
