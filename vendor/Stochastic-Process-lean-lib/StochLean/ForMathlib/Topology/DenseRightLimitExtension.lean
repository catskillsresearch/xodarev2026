/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Order.LeftRightLim

/-! # Regularity of a function specified by right limits on a subset

Right limits on a subset determine a right-continuous extension, provided the
corresponding one-sided filters are nontrivial. A left limit on the subset
also becomes the left limit of the extension. No agreement with the original
function at the boundary points is assumed or asserted.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] [T3Space β] {D : Set α} {f g : α → β}

omit [OrderTopology α] in
theorem continuousWithinAt_of_right_limits_on_subset
    (hne : ∀ c, (nhdsWithin c (D ∩ Ioi c)).NeBot)
    (hr : ∀ c, Tendsto f (nhdsWithin c (D ∩ Ioi c)) (𝓝 (g c))) (a : α) :
    ContinuousWithinAt g (Ici a) a := by
  change Tendsto g (nhdsWithin a (Ici a)) (𝓝 (g a))
  apply (closed_nhds_basis (g a)).tendsto_right_iff.mpr
  rintro S ⟨hS, hSc⟩
  obtain ⟨U, hUo, haU, hU⟩ := mem_nhdsWithin.mp ((hr a).eventually hS)
  filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds haU),
    self_mem_nhdsWithin (a := a) (s := Ici a)] with c hc hac
  let := hne c
  apply hSc.mem_of_tendsto (hr c)
  filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hc),
    self_mem_nhdsWithin (a := c) (s := D ∩ Ioi c)] with x hx hDx
  exact hU ⟨hx, hDx.1, hac.trans_lt hDx.2⟩

theorem tendsto_right_limits_on_subset_from_left
    (hne : ∀ c, (nhdsWithin c (D ∩ Ioi c)).NeBot)
    (hr : ∀ c, Tendsto f (nhdsWithin c (D ∩ Ioi c)) (𝓝 (g c)))
    {a : α} {z : β} (hl : Tendsto f (nhdsWithin a (D ∩ Iio a)) (𝓝 z)) :
    Tendsto g (nhdsWithin a (Iio a)) (𝓝 z) := by
  apply (closed_nhds_basis z).tendsto_right_iff.mpr
  rintro S ⟨hS, hSc⟩
  obtain ⟨U, hUo, haU, hU⟩ := mem_nhdsWithin.mp (hl.eventually hS)
  filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds haU),
    self_mem_nhdsWithin (a := a) (s := Iio a)] with c hc hca
  let := hne c
  apply hSc.mem_of_tendsto (hr c)
  filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hc),
    nhdsWithin_le_nhds (Iio_mem_nhds hca),
    self_mem_nhdsWithin (a := c) (s := D ∩ Ioi c)] with x hx hxa hDx
  exact hU ⟨hx, hDx.1, hxa⟩
