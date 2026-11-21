/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Order.LeftRightLim

/-! # Left limits of the strict-right-limit function

The statement also covers a bottom endpoint, where the strict-left filter is bottom.
It does not require a globally bottom-free time order.
-/

@[expose] public section

open Function Filter Set
open scoped Topology

variable {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace E] [T3Space E]

theorem ContinuousWithinAt.tendsto_rightLim_nhdsLT {f : α → E} {a : α}
    (h : ContinuousWithinAt f (Iic a) a) :
    Tendsto f.rightLim (𝓝[<] a) (𝓝 (f a)) := by
  rcases eq_or_neBot (𝓝[<] a) with hbot | hne
  · rw [hbot]
    exact tendsto_bot
  · obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
      Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a) (s := Iio a))
    apply (closed_nhds_basis (f a)).tendsto_right_iff.mpr
    rintro s ⟨hs, hc⟩
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' hb).mp (h hs)
    filter_upwards [Ioo_mem_nhdsLT hu] with c hcu
    apply hc.mem_of_mapClusterPt ((mapClusterPt_rightLim f c).mono nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhds hcu.1 hcu.2] with d hd
    exact hsub ⟨hd.1, hd.2.le⟩
