/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RegularizationOneSidedLimits
public import StochLean.Probability.Martingale.Convergence.AntitoneSampling

/-! # Integrability and L1 approximation of the actual dyadic right limits

Antitone deterministic samples are uniformly integrable before path regularity
is known. Their almost-sure limits identify the constructed dyadic extension,
so its coordinates are integrable and decreasing right-side samples converge
to them in L1. Equality with the original coordinate is not yet assumed.
-/

@[expose] public section

open StochLean ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {e : ℕ → ℝ≥0} {t : ℝ≥0}

theorem Supermartingale.ae_tendsto_dyadicRightLimitProcess (hX : Supermartingale X F P)
    (hl : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 (dyadicRightLimitProcess X t ω)) :=
  hX.ae_exists_dyadic_one_sided_limits.mono fun _ hω ↦
    (tendsto_dyadicRightLimitProcess (hω t).1).comp hl

theorem Submartingale.ae_tendsto_dyadicRightLimitProcess (hX : Submartingale X F P)
    (hl : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 (dyadicRightLimitProcess X t ω)) :=
  hX.ae_exists_dyadic_one_sided_limits.mono fun _ hω ↦
    (tendsto_dyadicRightLimitProcess (hω t).1).comp hl

theorem Supermartingale.integrable_dyadicRightLimitProcess (hX : Supermartingale X F P)
    (t : ℝ≥0) : Integrable (dyadicRightLimitProcess X t) P := by
  obtain ⟨e, ha, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have he : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hu := hX.uniformIntegrable_antitone_reindex ha.antitone
  exact (hu.memLp_of_ae_tendsto (hX.ae_tendsto_dyadicRightLimitProcess he)).integrable le_rfl

theorem Submartingale.integrable_dyadicRightLimitProcess (hX : Submartingale X F P)
    (t : ℝ≥0) : Integrable (dyadicRightLimitProcess X t) P := by
  obtain ⟨e, ha, hm, hl⟩ := dyadicSkeleton_dense.exists_seq_strictAnti_tendsto t
  have he : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall fun n ↦ ⟨(hm n).2, (hm n).1⟩⟩
  have hu := hX.uniformIntegrable_antitone_reindex ha.antitone
  exact (hu.memLp_of_ae_tendsto (hX.ae_tendsto_dyadicRightLimitProcess he)).integrable le_rfl

theorem Supermartingale.tendsto_eLpNorm_dyadicRightLimitProcess (hX : Supermartingale X F P)
    (he : Antitone e) (hl : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t))) :
    Tendsto (fun n ↦ eLpNorm (X (e n) - dyadicRightLimitProcess X t) 1 P) atTop (𝓝 0) := by
  have hu := hX.uniformIntegrable_antitone_reindex he
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (memLp_one_iff_integrable.mpr (hX.integrable_dyadicRightLimitProcess t)) hu.2.1
    (hX.ae_tendsto_dyadicRightLimitProcess hl)

theorem Submartingale.tendsto_eLpNorm_dyadicRightLimitProcess (hX : Submartingale X F P)
    (he : Antitone e) (hl : Tendsto e atTop (nhdsWithin t (dyadicSkeleton ∩ Ioi t))) :
    Tendsto (fun n ↦ eLpNorm (X (e n) - dyadicRightLimitProcess X t) 1 P) atTop (𝓝 0) := by
  have hu := hX.uniformIntegrable_antitone_reindex he
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (memLp_one_iff_integrable.mpr (hX.integrable_dyadicRightLimitProcess t)) hu.2.1
    (hX.ae_tendsto_dyadicRightLimitProcess hl)

end MeasureTheory
