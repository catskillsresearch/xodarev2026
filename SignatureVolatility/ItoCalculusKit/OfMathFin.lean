module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ItoCalculusKit.DoleansSDE
public import SignatureVolatility.ItoCalculusKit.ItoQuadDoleans
public import SignatureVolatility.ItoCalculusKit.NovikovDoob
public import SignatureVolatility.ItoCalculusKit.StoppedL2
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper-strength `ItoCalculusKit` from MathFin (Phase 2)

**Status: ASSEMBLED.** Process fields from the dyadic limUnder bridge (`MathFinBridge` /
`ItoQuadDoleans`). `doleans_sde` (signature volatility under H1–H3 + pathwise continuity) is
proved for `d = 0` and, for `0 < d`, for constant `σ` (Black–Scholes: pathwise Föllmer–Itô +
almost-sure quadratic variation); the non-constant `0 < d` leaf is the axiom
`kit_doleans_sde_of_driver`. Analytic obligations `stopped_l2_localisation` and
`novikov_doob_l2_martingale` remain named axioms (envelope is a.e.; driver is
everywhere-continuous with independent coordinate *processes*).
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

end SignatureVolatility
