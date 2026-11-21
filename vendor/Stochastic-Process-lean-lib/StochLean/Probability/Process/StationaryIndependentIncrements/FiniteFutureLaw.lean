/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrements
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Stationarity of the actual finite future-increment vector

The original stationary independent-increment predicate determines the joint
law of every finite vector of increments from a deterministic starting time.
The reference vector subtracts the actual `X 0`; a zero initial value is not
assumed.

The existing finite-set order embedding sorts the requested lags together
with zero. Adjacent increments on this actual grid, extended constantly
after its last time, are jointly independent before and after the shift.
Their genuine marginal stationary laws give the joint law by native
`IdentDistrib.pi`. One measurable map of true telescoping partial sums then
recovers the requested vector, including repeated and zero lags.

No joint-law certificate, pairwise substitute, path regularity, Gaussian
assumption, or additional measurability hypothesis is used. The stationary
increment laws themselves provide the required marginal AE measurability.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.HasStationaryIndependentIncrements

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

/-- Any finite vector of genuine future increments is invariant in law under
a deterministic shift for a stationary independent-increment process. The
reference increments retain the original, possibly nonzero initial value. -/
theorem identDistrib_finite_future {I : Type*} [Finite I]
    (hX : HasStationaryIndependentIncrements X P) (s : ℝ≥0) (t : I → ℝ≥0) :
    IdentDistrib (fun ω i ↦ X (s + t i) ω - X s ω)
      (fun ω i ↦ X (t i) ω - X 0 ω) P P := by
  classical
  let := Fintype.ofFinite I
  let S : Finset ℝ≥0 := insert 0 (Finset.univ.image t)
  have hzero : 0 ∈ S := Finset.mem_insert_self _ _
  have hSne : S.Nonempty := ⟨0, hzero⟩
  obtain ⟨k, hcard⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Finset.card_pos.mpr hSne))
  let e : Fin (k + 1) ↪o ℝ≥0 := S.orderEmbOfFin hcard
  let v : ℕ → ℝ≥0 := fun j ↦ e ⟨min j k, Nat.lt_succ_of_le (min_le_right j k)⟩
  have hv : Monotone v := fun i j hij ↦ e.monotone (min_le_min_right k hij)
  have hv0 : v 0 = 0 := by
    simp only [v, Nat.zero_min]
    rw [show e ⟨0, Nat.lt_succ_of_le (min_le_right 0 k)⟩ = S.min' hSne from
      Finset.orderEmbOfFin_zero hcard (Nat.succ_pos k)]
    exact le_antisymm (S.min'_le 0 hzero) bot_le
  have htmem (i : I) : t i ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let idx : I → Fin (k + 1) := fun i ↦ (S.orderIsoOfFin hcard).symm ⟨t i, htmem i⟩
  have hidx (i : I) : v (idx i) = t i := by
    simp only [v, min_eq_left (Nat.le_of_lt_succ (idx i).isLt)]
    exact congrArg Subtype.val ((S.orderIsoOfFin hcard).apply_symm_apply ⟨t i, htmem i⟩)
  let Dshift : ℕ → Ω → ℝ := fun j ω ↦
    X (s + v (j + 1)) ω - X (s + v j) ω
  let Dref : ℕ → Ω → ℝ := fun j ω ↦ X (v (j + 1)) ω - X (v j) ω
  have hshift : iIndepFun Dshift P :=
    hX.indepIncrements.nat (t := fun j ↦ s + v j)
      (fun i j hij ↦ add_le_add le_rfl (hv hij))
  have href : iIndepFun Dref P := hX.indepIncrements.nat hv
  have hcoord (j : ℕ) : IdentDistrib (Dshift j) (Dref j) P P := by
    have hcancel : v j + (v (j + 1) - v j) = v (j + 1) :=
      add_tsub_cancel_of_le (hv (Nat.le_succ j))
    have hshiftcancel : (s + v j) + (v (j + 1) - v j) = s + v (j + 1) := by
      rw [add_assoc, hcancel]
    have hleft := hX.stationaryIncrements (s + v j) (v (j + 1) - v j)
    have hright := hX.stationaryIncrements (v j) (v (j + 1) - v j)
    simpa only [Dshift, Dref, hshiftcancel, hcancel] using hleft.trans hright.symm
  have hjoint : IdentDistrib (fun ω j ↦ Dshift j ω) (fun ω j ↦ Dref j ω) P P :=
    IdentDistrib.pi hcoord hshift href
  let Φ : (ℕ → ℝ) → I → ℝ := fun y i ↦ ∑ j ∈ Finset.range (idx i).val, y j
  have hΦ : Measurable Φ :=
    measurable_pi_iff.mpr fun i ↦
      Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hleft : Φ ∘ (fun ω j ↦ Dshift j ω) =
      (fun ω i ↦ X (s + t i) ω - X s ω) := by
    funext ω i
    change (∑ j ∈ Finset.range (idx i).val,
      (X (s + v (j + 1)) ω - X (s + v j) ω)) = _
    rw [Finset.sum_range_sub (fun j ↦ X (s + v j) ω) (idx i).val,
      hidx, hv0, add_zero]
  have hright : Φ ∘ (fun ω j ↦ Dref j ω) =
      (fun ω i ↦ X (t i) ω - X 0 ω) := by
    funext ω i
    change (∑ j ∈ Finset.range (idx i).val, (X (v (j + 1)) ω - X (v j) ω)) = _
    rw [Finset.sum_range_sub (fun j ↦ X (v j) ω) (idx i).val, hidx, hv0]
  have hresult := hjoint.comp hΦ
  rw [hleft, hright] at hresult
  exact hresult

end ProbabilityTheory.HasStationaryIndependentIncrements
