module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.TimeReindex


@[expose] public section

open MeasureTheory Filter Topology
open scoped Interval NNReal

noncomputable section

namespace SignatureVolatility

/-!
# Itô / Lebesgue adapters from `MultiBrownian` (length-2 surface)

Uses `Wnn` (Mathlib `ℝ≥0`-time BM) and closed-form Itô identities for length-2 words.
Lebesgue integrals of BM paths are defined as limits of dyadic Riemann sums (measurable in ω).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Space increment of coordinate `i` between `ℝ`-times `s` and `t` via `toNNReal`. -/
def wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  B.Wnn (Real.toNNReal t) ω i - B.Wnn (Real.toNNReal s) ω i

lemma measurable_wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) :
    Measurable (fun ω => wnnIncr B i s t ω) :=
  (B.Wnn_meas _ i).sub (B.Wnn_meas _ i)

/-- Dyadic left Riemann sum for `∫_s^t (W_u^i - W_s^i) du`. -/
def lebRiemann_wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ k ∈ Finset.range (n + 1),
    wnnIncr B i s (s + (k : ℝ) * Δ) ω * Δ

lemma measurable_lebRiemann_wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => lebRiemann_wnnIncr B i s t n ω) :=
  Finset.measurable_sum _ fun _ _ =>
    (measurable_wnnIncr B i s _).mul measurable_const

/-- Pathwise Lebesgue `∫_s^t (W_u^i - W_s^i) du` as the dyadic Riemann limit (0 if `¬ s ≤ t`
or if the limit fails — on a.s.-continuous BM paths the limit exists and matches
`intervalIntegral`). -/
def lebIntegral_wnnIncrement (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => lebRiemann_wnnIncr B i s t n ω else 0

lemma measurable_lebIntegral_wnnIncrement (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) :
    Measurable (fun ω => lebIntegral_wnnIncrement B i s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [lebIntegral_wnnIncrement, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_lebRiemann_wnnIncr B i s t n).stronglyMeasurable)).measurable
  · simp [lebIntegral_wnnIncrement, h]

/-- Closed form: `∫_s^t (u-s) du = (t-s)^2/2`. -/
def lebIntegral_timeIntegrand (s t : ℝ) : ℝ :=
  if s ≤ t then (t - s) ^ 2 / 2 else 0

/-- Closed-form Itô: `∫_s^t (u-s) dW^i = (t-s)(W_t^i-W_s^i) - ∫_s^t (W_u^i-W_s^i) du`. -/
def itoIntegral_timeIntegrand (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then
    (t - s) * wnnIncr B i s t ω - lebIntegral_wnnIncrement B i s t ω
  else 0

lemma measurable_itoIntegral_timeIntegrand (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_timeIntegrand B i s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [itoIntegral_timeIntegrand, h, ↓reduceDIte]
    exact (measurable_const.mul (measurable_wnnIncr B i s t)).sub
      (measurable_lebIntegral_wnnIncrement B i s t)
  · simp [itoIntegral_timeIntegrand, h]

/-- Closed-form Itô (same coordinate):
`∫_s^t (W_u^i - W_s^i) dW^i = ½((W_t^i-W_s^i)^2 - (t-s))`. -/
def itoIntegral_wnnIncrement_diag (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then
    (1 / 2 : ℝ) * (wnnIncr B i s t ω ^ 2 - (t - s))
  else 0

lemma measurable_itoIntegral_wnnIncrement_diag (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_wnnIncrement_diag B i s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [itoIntegral_wnnIncrement_diag, h, ↓reduceDIte]
    exact measurable_const.mul <|
      ((measurable_wnnIncr B i s t).pow_const 2).sub measurable_const
  · simp [itoIntegral_wnnIncrement_diag, h]

/-- Increment Itô against coordinate `k`. Diagonal uses the quadratic closed form.
Cross-coordinate (`i ≠ k`) uses the MathFin-facing hook `itoIntegral_wnnIncrement_cross`
(defined below as a dyadic Itô–Riemann limit). -/
def itoRiemann_wnnIncr (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ j ∈ Finset.range (n + 1),
    wnnIncr B i s (s + (j : ℝ) * Δ) ω *
      wnnIncr B k (s + (j : ℝ) * Δ) (s + ((j : ℝ) + 1) * Δ) ω

lemma measurable_itoRiemann_wnnIncr (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => itoRiemann_wnnIncr B i k s t n ω) :=
  Finset.measurable_sum _ fun _ _ =>
    (measurable_wnnIncr B i s _).mul (measurable_wnnIncr B k _ _)

/-- Cross (and general) Itô as dyadic left Riemann–Itô limit. -/
def itoIntegral_wnnIncrement_cross (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => itoRiemann_wnnIncr B i k s t n ω else 0

lemma measurable_itoIntegral_wnnIncrement_cross (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_wnnIncrement_cross B i k s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [itoIntegral_wnnIncrement_cross, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_itoRiemann_wnnIncr B i k s t n).stronglyMeasurable)).measurable
  · simp [itoIntegral_wnnIncrement_cross, h]

/-- Dispatch: diagonal closed form, else dyadic Itô–Riemann limit. -/
def itoIntegral_wnnIncrement (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  if i = k then itoIntegral_wnnIncrement_diag B i s t ω
  else itoIntegral_wnnIncrement_cross B i k s t ω

lemma measurable_itoIntegral_wnnIncrement (B : MultiBrownian Ω P d) (i k : Fin d) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_wnnIncrement B i k s t ω) := by
  classical
  by_cases hik : i = k
  · simpa [itoIntegral_wnnIncrement, hik] using measurable_itoIntegral_wnnIncrement_diag B i s t
  · simpa [itoIntegral_wnnIncrement, hik] using measurable_itoIntegral_wnnIncrement_cross B i k s t

end SignatureVolatility
