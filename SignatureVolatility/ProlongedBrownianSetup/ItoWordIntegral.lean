module

public import SignatureVolatility.ProlongedBrownianSetup.ContVersion
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralConsLong
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe2


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Word-indexed Itô iterated integrals of the prolonged path `(t, W)`

Local-hole-free packer: level ≤1 from `ItoWordIntegralLe1`, length-2 from `ItoWordIntegralLe2`,
longer words from `ItoWordIntegralConsLong` with previous process `H u = itoWordIntegral … I`.
Every level `≥ 2` is replaced by its adapted continuous version (`ContVersion`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- One Itô step at upper time `u` for the word `j :: I` (`I ≠ []`), given the previous
coordinate process `H` of `I`; `0` for `u < s`. -/
def itoWordStep (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (I : Word (d + 1))
    (H : ℝ → Ω → ℝ) (s u : ℝ) (ω : Ω) : ℝ :=
  if s ≤ u then
    if h : I.length = 1 then itoWordIntegral_le2 B j I h s u ω
    else itoWordIntegral_cons_long B j H s u ω
  else 0

/-- Word-indexed Itô iterated integral of `wAug` over `[s,t]`. Levels `≥ 2` are taken as
their adapted continuous versions (`contVersion`) before being integrated further. -/
def itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I = [] then itoWordIntegral_le1 B s t ω [j]
    else
      contVersion (itoWordStep B j I (fun u ω' => itoWordIntegral B s u ω' I) s) t ω

lemma itoWordIntegral_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [] = 1 := rfl

lemma itoWordIntegral_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [0] = t - s := by
  simp [itoWordIntegral, itoWordIntegral_le1_time]

lemma itoWordIntegral_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    itoWordIntegral B s t ω [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [itoWordIntegral, itoWordIntegral_le1_space]

lemma measurable_itoWordStep (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (I : Word (d + 1))
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s u : ℝ) :
    Measurable (fun ω => itoWordStep B j I H s u ω) := by
  unfold itoWordStep
  by_cases hsu : s ≤ u
  · by_cases hlen : I.length = 1
    · simpa [hsu, hlen] using measurable_itoWordIntegral_le2 B j I hlen s u
    · simpa [hsu, hlen] using measurable_itoWordIntegral_cons_long B j H hH s u
  · simp [hsu]

lemma measurable_itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral B s t ω I) := by
  match I with
  | [] => simp [itoWordIntegral]
  | j :: I' =>
    by_cases hI : I' = []
    · subst hI
      simpa [itoWordIntegral] using measurable_itoWordIntegral_le1 B s t [j]
    · simp only [itoWordIntegral, hI, ↓reduceIte]
      exact measurable_contVersion _ t fun n => measurable_itoWordStep B j I' _
        (fun u => measurable_itoWordIntegral B s u I') s _

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
