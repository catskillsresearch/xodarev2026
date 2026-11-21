/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Stability
public import StochLean.Probability.Process.Measurability.InitialMask

/-! # Indistinguishable versions of the existing local-martingale predicates

The actual fundamental sequence is retained, including its initial masks.
Adaptedness of the target is explicit; no measurability of arbitrary versions
is silently assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsUIMartingale.congr (hX : IsUIMartingale X F P)
    (ha : Adapted F Y) (he : Indistinguishable X Y P) : IsUIMartingale Y F P :=
  ⟨hX.1.congr ha.stronglyAdapted he.ae_eq, hX.2.ae_eq he.ae_eq⟩

theorem IsLocalMartingale.congr (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) (ha : Adapted F Y) (he : Indistinguishable X Y P) :
    IsLocalMartingale Y F P := by
  have hc := hX.2.1.congr he
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨ha, hc, τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hs : MeasurableSet[F 0] {ω | 0 < τ n ω} :=
    (hτ.1.isStoppingTime n).measurableSet_gt 0
  have hmask := ha.indicator_initial hs
  exact (hτ.2.2 n).congr
    (hmask.stronglyAdapted.stoppedProcess_of_usual hF
      (hc.indicator {ω | 0 < τ n ω}).hasRightContinuousPaths (hτ.1.isStoppingTime n)).adapted
    ((he.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n))

theorem IsContinuousLocalMartingale.congr (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) (ha : Adapted F Y) (he : Indistinguishable X Y P) :
    IsContinuousLocalMartingale Y F P :=
  ⟨hX.1.congr hF ha he, hX.2.congr he⟩

end ProbabilityTheory
