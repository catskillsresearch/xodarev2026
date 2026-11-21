/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalCountableSampling
public import StochLean.Probability.Process.Stopping.Approximation
public import StochLean.Probability.Process.Path.RightContinuous

/-! # Constant conditional projections at arbitrary finite stopping times

Actual upper dyadic stopping grids, countable-coordinate measurability,
common-event right continuity and dominated conditional convergence extend
a constant deterministic conditional projection to any genuinely finite
stopping time. The input process need not be adapted or jointly measurable.
The dominating random variable controls all times on one common event.
No deterministic bound on the stopping time or usualness is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {V : ℝ≥0 → Ω → ℝ}

/-- A dominated right-continuous process whose deterministic conditional
projections are constant has the same conditional projection at every
genuinely finite stopping time, without a joint-measurability assumption. -/
theorem sample_condExp_const_of_dominated_rightContinuous
    (τ : FiniteStoppingTime F) (hmV : ∀ s, Measurable (V s))
    (hr : HasRightContinuousPaths V P) {g : Ω → ℝ} (hg : Integrable g P)
    (hb : ∀ᵐ ω ∂P, ∀ s, ‖V s ω‖ ≤ g ω) (c : ℝ)
    (hdet : ∀ s, P[V s | F s] =ᵐ[P] fun _ ↦ c) :
    P[(fun ω ↦ V (τ ω) ω) | τ.measurableSpace] =ᵐ[P] fun _ ↦ c := by
  let σ (n : ℕ) : FiniteStoppingTime F :=
    ⟨fun ω ↦ dyadicRightGrid n (τ ω), stoppingTime_dyadicRightGridFinite τ.isStoppingTime n⟩
  have hcount (n : ℕ) : (range (σ n)).Countable := by
    apply (countable_range_dyadicRightGrid n).mono
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, rfl⟩
  have hle (n : ℕ) (ω : Ω) : τ ω ≤ σ n ω := le_dyadicRightGrid n (τ ω)
  let Z (n : ℕ) (ω : Ω) := V (σ n ω) ω
  have hmZ (n : ℕ) : Measurable (Z n) := by
    let R := range (σ n)
    let : Countable R := (hcount n).to_subtype
    have hmσ : Measurable (σ n) :=
      ((σ n).isStoppingTime.measurable.untopD 0).mono (σ n).measurableSpace_le le_rfl
    have hmR : Measurable (fun ω ↦ (⟨σ n ω, mem_range_self ω⟩ : R)) :=
      hmσ.subtype_mk
    have hmEval : Measurable (fun p : Ω × R ↦ V p.2.val p.1) :=
      measurable_from_prod_countable_left fun r ↦ hmV r.val
    exact hmEval.comp (measurable_id.prodMk hmR)
  have hiV (s : ℝ≥0) : Integrable (V s) P :=
    hg.mono' (hmV s).aestronglyMeasurable (hb.mono fun _ hω ↦ hω s)
  have hiZ (n : ℕ) : Integrable (Z n) P :=
    hg.mono' (hmZ n).aestronglyMeasurable (hb.mono fun ω hω ↦ hω (σ n ω))
  have hZlim : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ Z n ω) atTop (𝓝 (V (τ ω) ω)) := by
    filter_upwards [hr] with ω hω
    exact (hω (τ ω)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_dyadicRightGrid (τ ω), Eventually.of_forall fun n ↦ hle n ω⟩)
  have hcond (n : ℕ) : P[Z n | (σ n).measurableSpace] =ᵐ[P] fun _ ↦ c :=
    ((σ n).sample_condExp_of_countable_range (hcount n) hiV (hiZ n)
      (Y := fun _ _ ↦ c) (fun s ↦ (hdet s).symm)).symm
  have hfg (n : ℕ) :
      P[Z n | τ.measurableSpace] =ᵐ[P] P[(fun _ : Ω ↦ c) | τ.measurableSpace] := by
    have hfields : τ.measurableSpace ≤ (σ n).measurableSpace :=
      τ.isStoppingTime.measurableSpace_mono (σ n).isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr (hle n ω))
    exact (condExp_condExp_of_le hfields (σ n).measurableSpace_le).symm.trans
      (condExp_congr_ae (hcond n))
  have hresult := tendsto_condExp_unique Z (fun _ _ ↦ c) (fun ω ↦ V (τ ω) ω) (fun _ ↦ c)
    hiZ (fun _ ↦ integrable_const c) hZlim
    (ae_of_all _ fun _ ↦ tendsto_const_nhds)
    g hg (fun _ ↦ ‖c‖) (integrable_const _)
    (fun n ↦ hb.mono fun ω hω ↦ hω (σ n ω))
    (fun _ ↦ ae_of_all _ fun _ ↦ le_rfl) hfg
  rw [condExp_const τ.measurableSpace_le c] at hresult
  exact hresult

end ProbabilityTheory.FiniteStoppingTime
