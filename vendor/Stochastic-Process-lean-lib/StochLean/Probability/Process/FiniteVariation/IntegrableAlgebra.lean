/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.Probability.Process.Path.Algebra
public import StochLean.ForMathlib.VariationAlgebra

/-! # Algebra of integrable variation

Negation and real constant multiplication have exact extended-variation
formulas, so they preserve integrable variation without process measurability
or path regularity assumptions. The zero scalar is included.

For sums, variation domination alone does not establish measurability of the
actual total variation. The basic result therefore explicitly requires its
almost-everywhere measurability. Adapted cadlag processes on a usual filtration
provide this hypothesis through the existing whole-half-line variation owner.
The subtraction results use the same argument and exact negation invariance.

Initial values remain arbitrary: no initial integrability or zero initial
condition is assumed. Extended variation is proved finite before converting
its order bounds to real values.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

private theorem eVariationOn_const_mul_path (c : ℝ) (x : ℝ≥0 → ℝ) :
    eVariationOn (fun t ↦ c * x t) univ = ENNReal.ofReal |c| * eVariationOn x univ := by
  have he (a b : ℝ) : edist (c * a) (c * b) = ENNReal.ofReal |c| * edist a b := by
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg c)]
  simp only [eVariationOn, he, ← Finset.mul_sum, ← ENNReal.mul_iSup]

/-- Exact negation invariance requires no additional measurability or path
regularity assumption. -/
theorem HasIntegrableVariation.neg (hX : HasIntegrableVariation X P) :
    HasIntegrableVariation (-X) P := by
  constructor
  · filter_upwards [hX.ae_eVariationOn_ne_top] with ω hω
    change eVariationOn (fun t ↦ -X t ω) univ ≠ ∞
    simpa only [eVariationOn_neg] using hω
  · simpa only [Pi.neg_apply, eVariationOn_neg] using hX.integrable_eVariationOn_toReal

/-- Constant multiplication retains the actual extended variation, including
the zero scalar and arbitrary initial random values. -/
theorem HasIntegrableVariation.const_mul (hX : HasIntegrableVariation X P) (c : ℝ) :
    HasIntegrableVariation (fun t ω ↦ c * X t ω) P := by
  constructor
  · filter_upwards [hX.ae_eVariationOn_ne_top] with ω hω
    change eVariationOn (fun t ↦ c * X t ω) univ ≠ ∞
    rw [eVariationOn_const_mul_path]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
  · simpa only [eVariationOn_const_mul_path, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg c)] using
        hX.integrable_eVariationOn_toReal.const_mul |c|

theorem HasIntegrableVariation.smul (hX : HasIntegrableVariation X P) (c : ℝ) :
    HasIntegrableVariation (c • X) P := by
  have he : c • X = fun t ω ↦ c * X t ω := by
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact hX.const_mul c

/-- Quantitative variation domination proves integrability once actual sum
variation is known almost everywhere measurable. This measurability premise
is not inferred from integrability of the two separate variations. -/
theorem HasIntegrableVariation.add_of_aemeasurable
    (hX : HasIntegrableVariation X P) (hY : HasIntegrableVariation Y P)
    (hm : AEMeasurable (fun ω ↦ eVariationOn ((X + Y) · ω) univ) P) :
    HasIntegrableVariation (X + Y) P := by
  have hbound (ω : Ω) : eVariationOn ((X + Y) · ω) univ ≤
      eVariationOn (X · ω) univ + eVariationOn (Y · ω) univ :=
    eVariationOn_add_le (X · ω) (Y · ω) univ
  constructor
  · filter_upwards [hX.ae_eVariationOn_ne_top, hY.ae_eVariationOn_ne_top] with ω hx hy
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hx, hy⟩) (hbound ω)
  · apply (hX.integrable_eVariationOn_toReal.add hY.integrable_eVariationOn_toReal).mono'
      hm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hX.ae_eVariationOn_ne_top, hY.ae_eVariationOn_ne_top] with ω hx hy
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hx, hy⟩) (hbound ω)
    simpa only [Pi.add_apply, ENNReal.toReal_add hx hy] using ht

/-- The difference version retains the same explicit actual-variation
measurability requirement. -/
theorem HasIntegrableVariation.sub_of_aemeasurable
    (hX : HasIntegrableVariation X P) (hY : HasIntegrableVariation Y P)
    (hm : AEMeasurable (fun ω ↦ eVariationOn ((X - Y) · ω) univ) P) :
    HasIntegrableVariation (X - Y) P := by
  simpa only [sub_eq_add_neg] using hX.add_of_aemeasurable hY.neg
    (by simpa only [sub_eq_add_neg] using hm)

variable {F : Filtration ℝ≥0 mΩ}

/-- Adapted cadlag paths on a usual filtration give exact measurability of
the actual sum variation; no measurability certificate is left to the caller. -/
theorem HasIntegrableVariation.add (hX : HasIntegrableVariation X P)
    (hY : HasIntegrableVariation Y P) (haX : Adapted F X) (haY : Adapted F Y)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasIntegrableVariation (X + Y) P := by
  have ha : Adapted F (X + Y) := fun t ↦ (haX t).add (haY t)
  exact hX.add_of_aemeasurable hY
    (ha.measurable_eVariationOn_univ_of_usual hF (hcX.add hcY)).aemeasurable

/-- Subtraction of actual adapted cadlag IV processes on a usual filtration. -/
theorem HasIntegrableVariation.sub (hX : HasIntegrableVariation X P)
    (hY : HasIntegrableVariation Y P) (haX : Adapted F X) (haY : Adapted F Y)
    (hF : F.IsUsual P) (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    HasIntegrableVariation (X - Y) P := by
  have he : -Y = fun t ω ↦ -Y t ω := by
    funext t ω
    rfl
  have hnY : HasCadlagPaths (-Y) P := by
    rw [he]
    exact hcY.continuous_comp continuous_neg
  simpa only [sub_eq_add_neg] using
    hX.add hY.neg haX (fun t ↦ (haY t).neg) hF hcX hnY

end ProbabilityTheory
