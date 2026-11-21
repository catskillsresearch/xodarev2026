module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralConsLong
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe2


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Word-indexed Itô iterated integrals of the prolonged path `(t, W)`

Local-hole-free packer: level ≤1 from `ItoWordIntegralLe1`, length-2 from `ItoWordIntegralLe2`,
longer words from `ItoWordIntegralConsLong` with previous process `H u = itoWordIntegral … I`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Word-indexed Itô iterated integral of `wAug` over `[s,t]`. -/
def itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I = [] then itoWordIntegral_le1 B s t ω [j]
    else if h : I.length = 1 then itoWordIntegral_le2 B j I h s t ω
    else
      itoWordIntegral_cons_long B j (fun u ω' => itoWordIntegral B s u ω' I) s t ω

lemma itoWordIntegral_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [] = 1 := rfl

lemma itoWordIntegral_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [0] = t - s := by
  simp [itoWordIntegral, itoWordIntegral_le1_time]

lemma itoWordIntegral_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    itoWordIntegral B s t ω [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [itoWordIntegral, itoWordIntegral_le1_space]

lemma measurable_itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral B s t ω I) := by
  match I with
  | [] => simp [itoWordIntegral]
  | j :: I' =>
    by_cases hI : I' = []
    · subst hI
      simpa [itoWordIntegral] using measurable_itoWordIntegral_le1 B s t [j]
    · by_cases hlen : I'.length = 1
      · simp only [itoWordIntegral, hI, ↓reduceIte, hlen, ↓reduceDIte]
        exact measurable_itoWordIntegral_le2 B j I' hlen s t
      · simp only [itoWordIntegral, hI, ↓reduceIte, hlen, ↓reduceDIte]
        exact measurable_itoWordIntegral_cons_long B j
          (fun u ω' => itoWordIntegral B s u ω' I')
          (fun u => measurable_itoWordIntegral B s u I') s t

/-- Package Itô word coordinates as an element of the extended tensor algebra. -/
def itoSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => itoWordIntegral B s t ω I⟩

lemma itoSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (itoSig2 B s t ω).coeff [] = 1 :=
  itoWordIntegral_empty B s t ω

lemma itoSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (itoSig2 B s t ω).coeff [0] = t - s :=
  itoWordIntegral_time B s t ω

lemma itoSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (itoSig2 B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  itoWordIntegral_space B s t ω i

lemma measurable_itoSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (itoSig2 B s t ω).coeff I) :=
  measurable_itoWordIntegral B s t I

end SignatureVolatility
