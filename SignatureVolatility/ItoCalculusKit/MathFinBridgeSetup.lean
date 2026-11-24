module

public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.SignatureFiltrationEqBrownianFiltration

@[expose] public section

open MeasureTheory


namespace SignatureVolatility

/-!
# Bridge lemmas tied to the Stratonovich paper setup

Kept apart from `MathFinBridge` so that the generic Itô kit does not depend on the
paper's signature setup (`StratonovichOfBM`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- For the Stratonovich paper setup, path filtration = Brownian filtration. -/
lemma pathFiltration_eq_brownianFiltration (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T) :
    pathFiltration B =
      (prolongedBrownianSetup_stratonovich_of_brownian B hT).brownianFiltration :=
  rfl

/-- Adaptedness of `kitItoInt` to the signature filtration of the paper setup. -/
lemma kitItoInt_adapted_signature (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (kitItoInt B H s.1) := by
  have hpath := kitItoInt_adapted_path B H t s
  rw [signature_filtration_eq_brownian_filtration
    (prolongedBrownianSetup_stratonovich_of_brownian B hT) t,
    ← pathFiltration_eq_brownianFiltration B hT]
  exact hpath

/-- Adaptedness of `kitQuadVar` to the signature filtration of the paper setup. -/
lemma kitQuadVar_adapted_signature (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (kitQuadVar B H s.1) := by
  have hpath := kitQuadVar_adapted_path B H t s
  rw [signature_filtration_eq_brownian_filtration
    (prolongedBrownianSetup_stratonovich_of_brownian B hT) t,
    ← pathFiltration_eq_brownianFiltration B hT]
  exact hpath

end SignatureVolatility
