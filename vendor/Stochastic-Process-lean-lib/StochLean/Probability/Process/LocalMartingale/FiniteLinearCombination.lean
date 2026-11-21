/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Stability
public import StochLean.Probability.Process.LocalMartingale.InitialValue

/-! # Finite linear combinations of continuous local martingales

All summands use the existing masked local-martingale predicate. Finite
addition uses its proved common localizers and does not impose initial moments.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.add (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsContinuousLocalMartingale (X + Y) F P := by
  refine ⟨hX.1.add hY.1 hF, ?_⟩
  filter_upwards [hX.2, hY.2] with ω hx hy
  exact hx.add hy

theorem IsContinuousLocalMartingale.const_mul (hX : IsContinuousLocalMartingale X F P)
    (c : ℝ) : IsContinuousLocalMartingale (fun t ω ↦ c * X t ω) F P := by
  refine ⟨hX.1.const_smul c, ?_⟩
  filter_upwards [hX.2] with ω hx
  exact continuous_const.mul hx

theorem isContinuousLocalMartingale_finset_sum {ι : Type*} (S : Finset ι)
    {X : ι → ℝ≥0 → Ω → ℝ} (hF : F.IsUsual P)
    (hX : ∀ i ∈ S, IsContinuousLocalMartingale (X i) F P) :
    IsContinuousLocalMartingale (∑ i ∈ S, X i) F P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    change IsContinuousLocalMartingale (fun _ _ ↦ (0 : ℝ)) F P
    exact isContinuousLocalMartingale_const_initial measurable_const
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hX i (Finset.mem_insert_self i S)).add
      (ih (fun j hj ↦ hX j (Finset.mem_insert_of_mem hj))) hF

theorem isContinuousLocalMartingale_finset_linearCombination {ι : Type*} (S : Finset ι)
    {X : ι → ℝ≥0 → Ω → ℝ} (hF : F.IsUsual P) (a : ι → ℝ)
    (hX : ∀ i ∈ S, IsContinuousLocalMartingale (X i) F P) :
    IsContinuousLocalMartingale (fun t ω ↦ ∑ i ∈ S, a i * X i t ω) F P := by
  have hsum := isContinuousLocalMartingale_finset_sum S hF
    (fun i hi ↦ (hX i hi).const_mul (a i))
  convert hsum using 1
  funext t ω
  simp only [Finset.sum_apply]

end ProbabilityTheory
