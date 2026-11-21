/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorPairLimit
public import StochLean.Analysis.PathVariation.Stopping

/-! # Jump-series convergence for partial quadratic-pair sums

Partition horizons may vary and only need eventually cover the fixed
evaluation time. Clipping retains repeated endpoints and the last partial
cell; no additional mesh rate or refinement assumption is introduced.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E]

theorem normSquareVariationSum_stop {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (x : ℝ≥0 → E) : normSquareVariationSum (π.stop T hT) x =
      normSquareVariationSum π (fun u ↦ x (min u T)) := rfl

theorem normSquarePairSum_stop_terminal {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) :
    normSquarePairSum (π.stop T hT) Φ x T = normSquarePairSum π Φ x T := by
  simp only [normSquarePairSum, TimePartition.left, TimePartition.right, TimePartition.stop,
    min_assoc, min_self]
  rfl

theorem tendsto_normSquarePairSum_stopped_cadlag_jump_series [ProperSpace E] {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, normSquareVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsum : Summable (fun s : Ioc 0 T ↦
      Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) :
    Tendsto (fun n ↦ normSquarePairSum (π n) Φ x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) := by
  classical
  let ρ : ℕ → TimePartition T := fun n ↦
    if h : T ≤ S n then (π n).stop T h else TimePartition.single T
  have hm : Tendsto (fun n ↦ ((ρ n).mesh : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ NNReal.coe_nonneg (ρ n).mesh)) _ hmesh
    filter_upwards [hT] with n hn
    simp only [ρ, dif_pos hn]
    exact_mod_cast (π n).mesh_stop_le hn
  have hb' : ∀ᶠ n in atTop, normSquareVariationSum (ρ n) x ≤ B := by
    filter_upwards [hT, hb] with n hn hbn
    simpa only [ρ, dif_pos hn, normSquareVariationSum_stop] using hbn
  apply (tendsto_normSquarePairSum_cadlag_jump_series hx hΦ hdiag hm hB hb' hsum).congr'
  filter_upwards [hT] with n hn
  simp only [ρ, dif_pos hn, normSquarePairSum_stop_terminal]

end StochLean
