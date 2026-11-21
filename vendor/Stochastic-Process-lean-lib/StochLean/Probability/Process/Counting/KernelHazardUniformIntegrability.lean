/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.KernelHazard
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Integrability of the actual stopped hazard under a lifetime kernel

The actual extended stopped-hazard expectation under the native history/lifetime
composition-product measure is finite. This first proves almost-sure finiteness
and then gives the real stopped hazard's integrability and occurrence-mass mean.

For uniform integrability over the whole halfline, the integer-time supremum of
the original extended stopped hazard is an actual integrable envelope: monotone
convergence bounds its extended expectation by the finite total history mass.
Only afterwards is its real value used to dominate the compensated closed count.
Uniform boundedness of first moments alone is not used as a UI criterion.

The envelope is a local proof expression, not another hazard or terminal-value
selector. Initial and infinite lifetime atoms are retained. There is no
martingale, predictability, or joint cadlag-path assumption or conclusion here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal ProbabilityTheory Topology

namespace ProbabilityTheory

variable {H : Type*} {mH : MeasurableSpace H}

/-- The original real stopped kernel hazard is integrable and has the
actual positive-arrival mean under the composition-product measure. -/
theorem integrable_stoppedProcess_eCumulativeHazard_compProd
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ] (t : ℝ≥0) :
    Integrable (fun p : H × WithTop ℝ≥0 ↦ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2)
      (η ⊗ₘ κ) ∧
      (∫ p : H × WithTop ℝ≥0, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2
        ∂(η ⊗ₘ κ)) =
        (η ⊗ₘ κ).real {p : H × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} := by
  let A : H × WithTop ℝ≥0 → ℝ≥0∞ := fun p ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2
  have hm : Measurable A := (measurable_eCumulativeHazard_kernel κ).comp
    (measurable_fst.prodMk (measurable_const.min measurable_snd).untopA)
  have he : (∫⁻ p, A p ∂(η ⊗ₘ κ)) =
      (η ⊗ₘ κ) {p : H × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} :=
    lintegral_stoppedProcess_eCumulativeHazard_compProd η κ t
  have hfinite : (∫⁻ p, A p ∂(η ⊗ₘ κ)) ≠ ∞ := by
    rw [he]
    exact measure_ne_top (η ⊗ₘ κ) _
  have hA : ∀ᵐ p ∂(η ⊗ₘ κ), A p < ∞ := ae_lt_top hm hfinite
  change Integrable (fun p ↦ (A p).toReal) (η ⊗ₘ κ) ∧
    (∫ p, (A p).toReal ∂(η ⊗ₘ κ)) = _
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hA, he]
  rfl

/-- The original closed count minus its history-dependent stopped kernel
hazard is uniformly integrable over all finite times, by a genuine single
integrable envelope under the actual composition-product measure. -/
theorem uniformIntegrable_singleJump_sub_hazard_compProd
    (η : Measure H) [IsFiniteMeasure η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsMarkovKernel κ] :
    UniformIntegrable (fun (t : ℝ≥0) (p : H × WithTop ℝ≥0) ↦
      (if p.2 ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal)
        id t p.2) 1 (η ⊗ₘ κ) := by
  classical
  let A : ℝ≥0 → H × WithTop ℝ≥0 → ℝ≥0∞ := fun t p ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2
  let Ainf : H × WithTop ℝ≥0 → ℝ≥0∞ := fun p ↦ ⨆ n : ℕ, A (n : ℝ≥0) p
  have hm (t : ℝ≥0) : Measurable (A t) := (measurable_eCumulativeHazard_kernel κ).comp
    (measurable_fst.prodMk (measurable_const.min measurable_snd).untopA)
  have hmono (p : H × WithTop ℝ≥0) : Monotone (fun t : ℝ≥0 ↦ A t p) := by
    intro s t hst
    change stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r)
      id s p.2 ≤ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2
    rw [stoppedProcess_eCumulativeHazard_eq_lintegral (κ p.1) s p.2,
      stoppedProcess_eCumulativeHazard_eq_lintegral (κ p.1) t p.2]
    exact lintegral_mono_set (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst))
  have hmonoNat : Monotone (fun n : ℕ ↦ A (n : ℝ≥0)) := by
    intro n m hnm p
    exact hmono p (by exact_mod_cast hnm)
  have hmInf : Measurable Ainf := Measurable.iSup fun n : ℕ ↦ hm (n : ℝ≥0)
  have hmean : (∫⁻ p, Ainf p ∂(η ⊗ₘ κ)) ≤ η univ := by
    change (∫⁻ p, ⨆ n : ℕ, A (n : ℝ≥0) p ∂(η ⊗ₘ κ)) ≤ η univ
    rw [lintegral_iSup (fun n : ℕ ↦ hm (n : ℝ≥0)) hmonoNat]
    refine iSup_le fun n ↦ ?_
    change (∫⁻ p : H × WithTop ℝ≥0, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id (n : ℝ≥0) p.2
      ∂(η ⊗ₘ κ)) ≤ η univ
    rw [lintegral_stoppedProcess_eCumulativeHazard_compProd η κ (n : ℝ≥0)]
    calc
      _ ≤ (η ⊗ₘ κ) univ := measure_mono (subset_univ _)
      _ = η univ := Measure.compProd_apply_univ
  have hmeanFinite : (∫⁻ p, Ainf p ∂(η ⊗ₘ κ)) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top η univ) hmean
  have hfinite : ∀ᵐ p ∂(η ⊗ₘ κ), Ainf p < ∞ := ae_lt_top hmInf hmeanFinite
  have hi : Integrable (fun p ↦ (Ainf p).toReal) (η ⊗ₘ κ) :=
    integrable_toReal_of_lintegral_ne_top hmInf.aemeasurable hmeanFinite
  let G : H × WithTop ℝ≥0 → ℝ := fun p ↦ 1 + (Ainf p).toReal
  have hiG : Integrable G (η ⊗ₘ κ) := (integrable_const (1 : ℝ)).add hi
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ G) 1 (η ⊗ₘ κ) :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hiG)
  apply hu.mono_norm
  · intro t
    have hcount : Measurable (fun p : H × WithTop ℝ≥0 ↦
        if p.2 ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_const)
        measurable_const measurable_const
    exact (hcount.sub (hm t).ennreal_toReal).stronglyMeasurable.aestronglyMeasurable
  intro t
  obtain ⟨n, htn⟩ := exists_nat_ge t
  filter_upwards [hfinite] with p hp
  have htInf : A t p ≤ Ainf p :=
    (hmono p htn).trans (le_iSup (fun n : ℕ ↦ A (n : ℝ≥0) p) n)
  have htFinite : A t p ≠ ∞ := ne_top_of_le_ne_top hp.ne htInf
  have hreal : (A t p).toReal ≤ (Ainf p).toReal :=
    (ENNReal.toReal_le_toReal htFinite hp.ne).mpr htInf
  have hcount : ‖if p.2 ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0‖ ≤ 1 := by
    split_ifs <;> norm_num
  change ‖(if p.2 ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) - (A t p).toReal‖ ≤ ‖G p‖
  apply (norm_sub_le _ _).trans
  have hnorm : ‖(A t p).toReal‖ ≤ (Ainf p).toReal := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hreal
  exact (add_le_add hcount hnorm).trans (le_abs_self (G p))

end ProbabilityTheory
