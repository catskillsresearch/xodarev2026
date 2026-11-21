/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Monotone convergence of extended nonnegative Lp norms

The supremum and its seminorm may be infinite. This form avoids taking a
real-valued supremum or assuming its finiteness before proving a maximal bound.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

theorem eLpNorm_iSup_of_monotone_ennreal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ℕ → Ω → ℝ≥0∞} (hm : ∀ n, Measurable (f n)) (hn : Monotone f)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun ω ↦ ⨆ n, f n ω) (ENNReal.ofReal p) P =
      ⨆ n, eLpNorm (f n) (ENNReal.ofReal p) P := by
  have hr (q : ℝ) (hq : 0 < q) (g : ℕ → ℝ≥0∞) :
      (⨆ n, g n) ^ q = ⨆ n, g n ^ q :=
    (ENNReal.orderIsoRpow q hq).map_iSup g
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  simp_rw [hr p hp]
  rw [lintegral_iSup (fun n ↦ (hm n).pow_const p)
    (fun i j hij ω ↦ ENNReal.rpow_le_rpow (hn hij ω) hp.le)]
  exact hr (1 / p) (one_div_pos.mpr hp) _

theorem ae_lt_top_of_eLpNorm_lt_top_ennreal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hm : AEMeasurable f P) {p : ℝ} (hp : 0 < p)
    (hb : eLpNorm f (ENNReal.ofReal p) P < ∞) : ∀ᵐ ω ∂P, f ω < ∞ := by
  have hi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hb
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp.le] at hi
  filter_upwards [ae_lt_top' (hm.pow_const p) hi.ne] with ω hω
  exact lt_top_iff_ne_top.mpr fun h ↦ hω.ne (by rw [h, ENNReal.top_rpow_of_pos hp])

end MeasureTheory
