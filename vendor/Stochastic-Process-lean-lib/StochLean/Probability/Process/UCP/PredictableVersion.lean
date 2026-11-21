/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.UniformConvergence
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # A UCP limit of predictable processes has a predictable version

The existing common-event locally uniform subsequence gives convergence
at every time on the same full-measure event. Mathlib's measurable limit
construction on the predictable sigma field then provides an actual
predictable version. Arbitrary exceptional paths of the original limit
are not declared predictable. No usual condition, path regularity,
adaptedness of the original limit, or finiteness of the measure is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.TendstoUCP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

/-- The conclusion is an indistinguishable predictable version, not
predictability of arbitrary original exceptional trajectories. -/
theorem exists_predictable_indistinguishable (hu : TendstoUCP P X atTop Y)
    (hp : ∀ n, IsStronglyPredictable F (X n)) :
    ∃ Z : ℝ≥0 → Ω → ℝ, Indistinguishable Y Z P ∧ IsStronglyPredictable F Z := by
  obtain ⟨k, _, hk⟩ := hu.exists_seq_ae_locallyUniform
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ X (k n) t ω)
  refine ⟨Z, ?_, ?_⟩
  · filter_upwards [hk] with ω hω t
    have ht : Tendsto (fun n ↦ X (k n) t ω) atTop (𝓝 (Y t ω)) :=
      (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hω t)).tendsto_at ⟨bot_le, le_rfl⟩
    exact ht.limUnder_eq.symm
  · let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    change StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ limUnder atTop (fun n ↦ X (k n) p.1 p.2))
    exact StronglyMeasurable.limUnder (fun n ↦ hp (k n))

end ProbabilityTheory.TendstoUCP
