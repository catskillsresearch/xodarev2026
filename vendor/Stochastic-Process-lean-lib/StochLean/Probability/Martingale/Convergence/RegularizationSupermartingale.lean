/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RegularizationModification

/-! # Supermartingale order of actual dyadic right limits

The canonical dyadic right-limit extension is a supermartingale under usual
conditions, without right-continuous expectations or a modification identity.
Its existing cadlag-path and L1 approximation theorems are reused. The samples
in the order proof approach the earlier time strictly from its right, inside
the interval between the two times, rather than an arbitrary grid rounding.

Nonnegativity and a right-continuous difference of two coordinates pass to
their right limits on common events using only the countable dyadic skeleton.
The two extensions individually need not be modifications of the inputs.
-/

@[expose] public section

open StochLean ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → ℝ}

/-- The actual dyadic right-limit extension of a real supermartingale remains
a supermartingale. No expectation continuity or modification is assumed. -/
theorem Supermartingale.supermartingale_dyadicRightLimitProcess
    (hX : Supermartingale X F P) (hF : F.IsUsual P) :
    Supermartingale (dyadicRightLimitProcess X) F P := by
  have ha := hX.stronglyAdapted_dyadicRightLimitProcess hF
  have hi := hX.integrable_dyadicRightLimitProcess
  refine ⟨ha, fun s t hst ↦ ?_, hi⟩
  rcases eq_or_lt_of_le hst with rfl | hst
  · rw [condExp_of_stronglyMeasurable (F.le s) (ha s) (hi s)]
  obtain ⟨e, he, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto_of_lt hst
  have ht : Tendsto e atTop (nhdsWithin s (dyadicSkeleton ∩ Ioi s)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1.1⟩⟩
  have hL1 := hX.tendsto_eLpNorm_dyadicRightLimitProcess he.antitone ht
  apply ae_of_ae_trim (F.le s)
  apply ae_le_of_forall_setIntegral_le
    (Integrable.trim (F.le s) integrable_condExp stronglyMeasurable_condExp)
    (Integrable.trim (F.le s) (hi s) (ha s))
  intro A hA _
  rw [← setIntegral_trim (F.le s) stronglyMeasurable_condExp hA,
    ← setIntegral_trim (F.le s) (ha s) hA, setIntegral_condExp (F.le s) (hi t) hA]
  apply ge_of_tendsto' (tendsto_setIntegral_of_L1' _ (hi s).aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable (e n)) hL1 A)
  intro n
  exact (integral_mono_ae (hi t).integrableOn (hX.integrable t).integrableOn
    (ae_restrict_of_ae (hX.dyadicRightLimitProcess_ae_le hF t))).trans
      (hX.setIntegral_le (hm n).1.2.le (F.mono (hm n).1.1.le A hA))

/-- Coordinatewise almost-sure nonnegativity becomes nonnegativity at all
times on one common event for the actual dyadic right-limit extension. -/
theorem Supermartingale.ae_forall_nonneg_dyadicRightLimitProcess
    (hX : Supermartingale X F P) (hn : ∀ t, 0 ≤ᵐ[P] X t) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ dyadicRightLimitProcess X t ω := by
  let : Countable dyadicSkeleton := dyadicSkeleton_countable.to_subtype
  have hd : ∀ᵐ ω ∂P, ∀ d : dyadicSkeleton, 0 ≤ X d ω :=
    ae_all_iff.mpr fun d ↦ hn d
  filter_upwards [hd, hX.ae_exists_dyadic_one_sided_limits] with ω hdω hlω t
  let := dyadicSkeleton_right_neBot t
  apply ge_of_tendsto (tendsto_dyadicRightLimitProcess (hlω t).1)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact hdω ⟨u, hu.1⟩

/-- A coordinatewise right-continuous difference survives simultaneous dyadic
right limits indistinguishably, even when neither coordinate is its own
right-limit modification. Only the countable skeleton identities are combined. -/
theorem Supermartingale.indistinguishable_sub_dyadicRightLimitProcess
    (hX : Supermartingale X F P) (hY : Supermartingale Y F P)
    (hZ : HasRightContinuousPaths Z P) (he : ∀ t, X t - Y t =ᵐ[P] Z t) :
    Indistinguishable (dyadicRightLimitProcess X - dyadicRightLimitProcess Y) Z P := by
  let : Countable dyadicSkeleton := dyadicSkeleton_countable.to_subtype
  have hd : ∀ᵐ ω ∂P, ∀ d : dyadicSkeleton, X d ω - Y d ω = Z d ω :=
    ae_all_iff.mpr fun d ↦ he d
  filter_upwards [hd, hX.ae_exists_dyadic_one_sided_limits,
    hY.ae_exists_dyadic_one_sided_limits, hZ] with ω hdω hxω hyω hzω t
  let := dyadicSkeleton_right_neBot t
  have hxy := (tendsto_dyadicRightLimitProcess (hxω t).1).sub
    (tendsto_dyadicRightLimitProcess (hyω t).1)
  have hz : Tendsto (fun u ↦ Z u ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t))
      (𝓝 (Z t ω)) :=
    (hzω t).tendsto.mono_left
      (nhdsWithin_mono t (fun u hu ↦ show t ≤ u from hu.2.le))
  have hxyZ : Tendsto (fun u ↦ Z u ω) (nhdsWithin t (dyadicSkeleton ∩ Ioi t))
      (𝓝 (dyadicRightLimitProcess X t ω - dyadicRightLimitProcess Y t ω)) := by
    apply hxy.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hdω ⟨u, hu.1⟩
  exact tendsto_nhds_unique hxyZ hz

end MeasureTheory
