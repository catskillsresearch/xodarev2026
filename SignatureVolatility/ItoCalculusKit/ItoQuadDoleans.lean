module

public import SignatureVolatility.ItoCalculusKit.MathFinBridge


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Process packaging for `itoCalculusKit_of_mathfin`

Thin aliases of the MathFin bridge Itô / QV / Doléans processes over `paperSetup`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Paper-setup Itô integral. -/
abbrev paperItoInt {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun H t ω => kitItoInt B H t ω

/-- Paper-setup quadratic variation. -/
abbrev paperQuadVar {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun H t ω => kitQuadVar B H t ω

/-- Paper-setup Doléans exponential. -/
abbrev paperDoleansExp {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun σ t ω => kitDoleansExp B σ t ω

lemma paperItoInt_zero {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (ω : Ω) :
    paperItoInt B hT H 0 ω = 0 :=
  kitItoInt_zero B H ω

lemma paperItoInt_meas {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (paperItoInt B hT H t) :=
  kitItoInt_meas B H t

lemma paperItoInt_adapted {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (paperItoInt B hT H s.1) :=
  kitItoInt_adapted_signature B hT H t s

lemma paperQuadVar_zero {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (ω : Ω) :
    paperQuadVar B hT H 0 ω = 0 :=
  kitQuadVar_zero B H ω

lemma paperQuadVar_meas {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (paperQuadVar B hT H t) :=
  kitQuadVar_meas B H t

lemma paperQuadVar_adapted {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (paperQuadVar B hT H s.1) :=
  kitQuadVar_adapted_signature B hT H t s

lemma paperDoleansExp_def {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    paperDoleansExp B hT σ t ω =
      Real.exp (paperItoInt B hT σ t ω - (1 / 2 : ℝ) * paperQuadVar B hT σ t ω) :=
  kitDoleansExp_def B σ t ω

end SignatureVolatility
