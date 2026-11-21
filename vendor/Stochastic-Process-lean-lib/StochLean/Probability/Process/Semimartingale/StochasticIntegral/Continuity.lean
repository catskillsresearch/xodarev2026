/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.UCP.Diagonal

/-! # UCP continuity of the constructed Chapter II integral

Each integrand is approximated by actual simple processes. A simultaneous
diagonal controls both input and integral errors, proving continuity on the
whole adapted-caglad domain, not just on the dense simple subclass.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ} {K : ℕ → ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : ∀ n, Adapted F (K n)) (hrK : ∀ n, HasCagladPaths (K n) P)
    (hu : TendstoUCP P K atTop H) :
    TendstoUCP P (fun n ↦ hX.stochasticIntegral hF (haK n) (hrK n)) atTop
      (hX.stochasticIntegral hF haH hrH) := by
  choose A hA huA using fun n ↦ exists_simplePredictable_tendstoUCP (haK n) hF (hrK n)
  have hJA : ∀ n, TendstoUCP P (fun k ↦ (hA n k).elementaryIntegralProcess X) atTop
      (hX.stochasticIntegral hF (haK n) (hrK n)) := fun n ↦
    hX.tendstoUCP_stochasticIntegral_of_simple hF (haK n) (hrK n) (hA n) (huA n)
  obtain ⟨k, hdiA, hdiJ⟩ := exists_diagonal_tendstoUCP_sub_zero huA hJA
  have hinput : TendstoUCP P (fun n ↦ A n (k n)) atTop H := by
    simpa only [sub_add_cancel, zero_add] using hdiA.add hu
  have houtput := hX.tendstoUCP_stochasticIntegral_of_simple hF haH hrH
    (fun n ↦ hA n (k n)) hinput
  simpa only [neg_sub, sub_add_cancel, neg_zero, zero_add] using hdiJ.neg.add houtput

end ProbabilityTheory
