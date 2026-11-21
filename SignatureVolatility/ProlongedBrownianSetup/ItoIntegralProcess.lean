module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM


@[expose] public section

open MeasureTheory Filter

noncomputable section

namespace SignatureVolatility

/-!
# Dyadic Lebesgue / Itô integrals of an arbitrary process

Generalizes the BM-only Riemann limits in `ItoIntegralAgainstBM` to a process
`H : ℝ → Ω → ℝ` (e.g. a previous signature word coordinate). Measurability assumes
`∀ u, Measurable (H u)`; a.s. convergence is deferred.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Dyadic left Riemann sum for `∫_s^t H_u du`. -/
def lebRiemann_process (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ k ∈ Finset.range (n + 1), H (s + (k : ℝ) * Δ) ω * Δ

lemma measurable_lebRiemann_process (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u))
    (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => lebRiemann_process H s t n ω) :=
  Finset.measurable_sum _ fun _ _ => (hH _).mul measurable_const

/-- Pathwise Lebesgue `∫_s^t H_u du` as dyadic Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def lebIntegral_process (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => lebRiemann_process H s t n ω else 0

lemma measurable_lebIntegral_process (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u))
    (s t : ℝ) :
    Measurable (fun ω => lebIntegral_process H s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [lebIntegral_process, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_lebRiemann_process H hH s t n).stronglyMeasurable)).measurable
  · simp [lebIntegral_process, h]

/-- Dyadic left Itô–Riemann sum for `∫_s^t H_u dW^k`. -/
def itoRiemann_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ j ∈ Finset.range (n + 1),
    H (s + (j : ℝ) * Δ) ω *
      wnnIncr B k (s + (j : ℝ) * Δ) (s + ((j : ℝ) + 1) * Δ) ω

lemma measurable_itoRiemann_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => itoRiemann_process B k H s t n ω) :=
  Finset.measurable_sum _ fun _ _ =>
    (hH _).mul (measurable_wnnIncr B k _ _)

/-- Pathwise Itô `∫_s^t H_u dW^k` as dyadic Itô–Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def itoIntegral_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => itoRiemann_process B k H s t n ω else 0

lemma measurable_itoIntegral_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_process B k H s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [itoIntegral_process, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_itoRiemann_process B k H hH s t n).stronglyMeasurable)).measurable
  · simp [itoIntegral_process, h]

end SignatureVolatility
