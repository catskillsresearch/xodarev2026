/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Uniform convergence controls the values of existing filter limits -/

@[expose] public section

open Filter Set
open scoped Topology

theorem TendstoUniformlyOn.tendsto_limit_values {α E ι : Type*} [MetricSpace E]
    {F : ι → α → E} {f : α → E} {s : Set α} {p : Filter ι} {q : Filter α} [q.NeBot]
    {L : ι → E} {y : E} (h : TendstoUniformlyOn F f p s) (hq : q ≤ 𝓟 s)
    (hF : ∀ i, Tendsto (F i) q (𝓝 (L i))) (hf : Tendsto f q (𝓝 y)) :
    Tendsto L p (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (ε / 2) (half_pos hε)] with i hi
  have hd : dist y (L i) ≤ ε / 2 := by
    apply le_of_tendsto (hf.dist (hF i))
    filter_upwards [le_principal_iff.mp hq] with x hx
    exact (hi x hx).le
  rw [dist_comm]
  exact hd.trans_lt (half_lt_self hε)
