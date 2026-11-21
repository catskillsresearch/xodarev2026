module

public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral
public import SignatureVolatility.Word


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Triangular Stratonovich ↔ Itô conversion for prolonged signature coordinates

Paper Appendix (“Detailed Stratonovich–Itô conversion”): for each word `I`,

\[
S^I_t = I^I_t + \sum_{J:|J|\le|I|-2} a_{I,J}\, I^J_t,
\]

with combinatorial coefficients `a_{I,J}` from adjacent Brownian bracket contractions.
Level `≤ 1` has no correction (Stratonovich = Itô). The dual/generator shadow of the
leading double-space contraction is `stratonovichHalfLaplacian` (used in Riccati).

**Status.** Level-`≤1` identity is proved by definition. The general triangular correction
sum for `|I| ≥ 2` is a HOLE.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Combinatorial conversion coefficient `a_{I,J}` (Appendix). -/
def stratItoCoeff (I J : Word (d + 1)) : ℝ := by
  -- Enumerate adjacent double-space contractions.
  sorry

/-- Correction polynomial. Vanishes for `|I| ≤ 1`; for longer words, finite sum of
`stratItoCoeff I J * itoWordIntegral … J` over `|J| ≤ |I| - 2`. -/
def stratItoCorrection (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    Word (d + 1) → ℝ
  | [] => 0
  | [_] => 0
  | _ :: _ :: _ => by
      -- Finite sum over contracted words; HOLE until `stratItoCoeff` is wired.
      sorry

lemma stratItoCorrection_of_length_le_one (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (I : Word (d + 1)) (hI : I.length ≤ 1) :
    stratItoCorrection B s t ω I = 0 := by
  match I with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ =>
    simp at hI

/-- Stratonovich word coordinate via triangular conversion from Itô. -/
def stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (I : Word (d + 1)) : ℝ :=
  itoWordIntegral B s t ω I + stratItoCorrection B s t ω I

lemma stratWordIntegral_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    stratWordIntegral B s t ω [] = 1 := by
  simp [stratWordIntegral, itoWordIntegral_empty, stratItoCorrection]

lemma stratWordIntegral_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    stratWordIntegral B s t ω [0] = t - s := by
  simp [stratWordIntegral, itoWordIntegral_time, stratItoCorrection]

lemma stratWordIntegral_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    stratWordIntegral B s t ω [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [stratWordIntegral, itoWordIntegral_space, stratItoCorrection]

lemma measurable_stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => stratWordIntegral B s t ω I) := by
  match I with
  | [] =>
    simp only [stratWordIntegral, stratItoCorrection, add_zero]
    exact measurable_itoWordIntegral B s t []
  | [_] =>
    simp only [stratWordIntegral, stratItoCorrection, add_zero]
    exact measurable_itoWordIntegral B s t _
  | _ :: _ :: _ =>
    -- Correction term for `|I| ≥ 2` once `stratItoCoeff` is defined.
    sorry

/-- Package Stratonovich word coordinates as an extended tensor series. -/
def stratSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I⟩

lemma stratSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (stratSig2 B s t ω).coeff [] = 1 :=
  stratWordIntegral_empty B s t ω

lemma stratSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (stratSig2 B s t ω).coeff [0] = t - s :=
  stratWordIntegral_time B s t ω

lemma stratSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (stratSig2 B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  stratWordIntegral_space B s t ω i

lemma measurable_stratSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (stratSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral B s t I

end SignatureVolatility
