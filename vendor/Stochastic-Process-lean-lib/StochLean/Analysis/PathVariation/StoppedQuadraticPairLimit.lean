/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagQuadraticPairLimit
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

theorem quadraticPairSum_stop_terminal {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) :
    quadraticPairSum (π.stop T hT) Φ x T = quadraticPairSum π Φ x T := by
  simp only [quadraticPairSum, TimePartition.left, TimePartition.right, TimePartition.stop,
    min_assoc, min_self]
  rfl

theorem tendsto_quadraticPairSum_stopped_cadlag_jump_series {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, quadraticVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsum : Summable (fun s : Ioc 0 T ↦
      Φ (Function.leftLim x s) (x s) * (x s - Function.leftLim x s) ^ 2)) :
    Tendsto (fun n ↦ quadraticPairSum (π n) Φ x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        Φ (Function.leftLim x s) (x s) * (x s - Function.leftLim x s) ^ 2)) := by
  classical
  let ρ : ℕ → TimePartition T := fun n ↦
    if h : T ≤ S n then (π n).stop T h else TimePartition.single T
  have hm : Tendsto (fun n ↦ ((ρ n).mesh : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ NNReal.coe_nonneg (ρ n).mesh)) _ hmesh
    filter_upwards [hT] with n hn
    simp only [ρ, dif_pos hn]
    exact_mod_cast (π n).mesh_stop_le hn
  have hb' : ∀ᶠ n in atTop, quadraticVariationSum (ρ n) x ≤ B := by
    filter_upwards [hT, hb] with n hn hbn
    simpa only [ρ, dif_pos hn, quadraticVariationSum_stop] using hbn
  apply (tendsto_quadraticPairSum_cadlag_jump_series hx hΦ hdiag hm hB hb' hsum).congr'
  filter_upwards [hT] with n hn
  simp only [ρ, dif_pos hn, quadraticPairSum_stop_terminal]

end StochLean
