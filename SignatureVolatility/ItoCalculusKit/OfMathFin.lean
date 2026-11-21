module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper-strength `ItoCalculusKit` from MathFin (Phase 2)

**Status: HOLE.** Kit inhabitant only. Paper Theorem A lives in
`TheoremA` (depends on this module).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Abbreviation: paper-strength prolonged setup from a multi-Brownian driver. -/
noncomputable abbrev paperSetup {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :=
  prolongedBrownianSetup_stratonovich_of_brownian B hT

/-- **Paper goal.** Nontrivial `ItoCalculusKit` over the Stratonovich prolonged setup. -/
noncomputable def itoCalculusKit_of_mathfin {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ItoCalculusKit Ω P d T (paperSetup B hT) := by
  -- Wire: MathFin `itoProcessCLM` / localised Ito, `ItoProcessQV`, `contDoleansExp`,
  -- `ItoFormulaGBM`, SDE uniqueness + Gronwall, local Novikov from H3 + factorial moments.
  sorry

end SignatureVolatility
