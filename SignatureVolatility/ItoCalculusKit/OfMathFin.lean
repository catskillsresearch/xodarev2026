module

public import SignatureVolatility.ItoCalculusKit.DoleansSDE
public import SignatureVolatility.ItoCalculusKit.StoppedL2
public import SignatureVolatility.ItoCalculusKit.DoleansStrongClass


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Paper-strength `ItoCalculusKit` from MathFin (Phase 2)

**Status: PROVED (no axioms, no `sorry`).** Process fields from the dyadic limUnder bridge
(`MathFinBridge` / `ItoQuadDoleans`). Every analytic field is a theorem: `doleans_sde`
(`DoleansSDE`), `stopped_l2_localisation` (`StoppedL2`, weighted-energy uniqueness),
`novikov_doob_l2_martingale` (`NovikovDoob`), `doleans_strong_class` (`DoleansStrongClass`).
`#print axioms itoCalculusKit_of_mathfin` reports only `propext`, `Classical.choice`, `Quot.sound`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Abbreviation: paper-strength prolonged setup from a multi-Brownian driver. -/
noncomputable abbrev paperSetup {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :=
  prolongedBrownianSetup_stratonovich_of_brownian B hT

/-- **Paper goal.** `ItoCalculusKit` over the Stratonovich prolonged setup. -/
noncomputable def itoCalculusKit_of_mathfin {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ItoCalculusKit Ω P d T (paperSetup B hT) where
  itoInt := paperItoInt B hT
  itoInt_zero := paperItoInt_zero B hT
  itoInt_meas := paperItoInt_meas B hT
  itoInt_adapted := paperItoInt_adapted B hT
  quadVar := paperQuadVar B hT
  quadVar_zero := paperQuadVar_zero B hT
  quadVar_meas := paperQuadVar_meas B hT
  quadVar_adapted := paperQuadVar_adapted B hT
  doleansExp := paperDoleansExp B hT
  doleansExp_def := paperDoleansExp_def B hT
  doleans_sde := kit_doleans_sde B hT
  stopped_l2_localisation := kit_stopped_l2_localisation B hT
  novikov_doob_l2_martingale := kit_novikov_doob_l2_martingale B hT
  doleans_strong_class := kit_doleans_strong_class B hT

end SignatureVolatility
