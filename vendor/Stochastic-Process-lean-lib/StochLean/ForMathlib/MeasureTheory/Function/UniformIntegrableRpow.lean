/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.DeLaValleePoussin
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Uniform integrability from a bounded moment above one -/

@[expose] public section

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] {f : ι → Ω → ℝ}

/-- Integrability of the positive `r`-th norm power is the concrete input
needed for real `L^r` membership. -/
theorem memLp_of_integrable_norm_rpow {g : Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : AEStronglyMeasurable g P) (hi : Integrable (fun ω ↦ ‖g ω‖ ^ r) P) :
    MemLp g (ENNReal.ofReal r) P := by
  have hleft : MemLp
      (fun ω ↦ ‖g ω‖ ^ (ENNReal.ofReal r).toReal) 1 P := by
    rw [ENNReal.toReal_ofReal hr.le]
    exact memLp_one_iff_integrable.mpr hi
  have h := (memLp_norm_rpow_iff (p := ENNReal.ofReal r) (q := ENNReal.ofReal r)
    hg (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top).mp (by
      convert hleft using 1
      rw [ENNReal.div_self (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top])
  simpa using h

/-- A uniformly bounded real `q`-moment, for `q > 1`, gives uniform
integrability. -/
theorem uniformIntegrable_of_bounded_nnnorm_rpow {q : ℝ} (hq : 1 < q)
    (hf : ∀ i : ι, AEStronglyMeasurable (f i) P) (C : ℝ≥0)
    (hb : ∀ i : ι, ∫⁻ ω, ((‖f i ω‖₊ ^ q : ℝ≥0) : ℝ≥0∞) ∂P ≤ (C : ℝ≥0∞)) :
    UniformIntegrable f 1 P := by
  let Φ : ℝ≥0 → ℝ≥0 := fun r ↦ r ^ q
  have hΦ : SuperlinearEnvelope Φ := by
    rw [SuperlinearEnvelope]
    have ht := NNReal.tendsto_rpow_atTop (sub_pos.mpr hq)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    change r ^ (q - 1) = r ^ q / r
    rw [NNReal.rpow_sub hr0.ne' q 1, NNReal.rpow_one]
  exact uniformIntegrable_of_superlinearEnvelope hΦ
    (NNReal.continuous_rpow_const (by linarith) |>.measurable) hf C hb

/-- A uniformly bounded real integral of a norm power above one is the
Bochner-integral form of the preceding de la Vallee-Poussin criterion. -/
theorem uniformIntegrable_of_bounded_integral_norm_rpow {q : ℝ} (hq : 1 < q)
    (hf : ∀ i : ι, AEStronglyMeasurable (f i) P)
    (hi : ∀ i : ι, Integrable (fun ω ↦ ‖f i ω‖ ^ q) P)
    (C : ℝ≥0) (hb : ∀ i : ι, integral P (fun ω ↦ ‖f i ω‖ ^ q) ≤ C) :
    UniformIntegrable f 1 P := by
  apply uniformIntegrable_of_bounded_nnnorm_rpow hq hf C
  intro i
  have heq : (fun ω ↦ ((‖f i ω‖₊ ^ q : ℝ≥0) : ℝ≥0∞)) =
      fun ω ↦ ENNReal.ofReal (‖f i ω‖ ^ q) := by
    funext ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hi i)
    (ae_of_all P fun ω ↦ Real.rpow_nonneg (norm_nonneg _) q)]
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hb i)

end MeasureTheory
