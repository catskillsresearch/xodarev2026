/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Stopping
public import StochLean.ForMathlib.VariationAlgebra

/-! # Finite variation on a stopped interval

Finite variation on an open interval extends to its endpoints for a cadlag
real path. The right endpoint contributes its actual jump, through Mathlib's
variation/one-sided-limit identity. Clamping and centering then give a finite-
variation stopped increment, including a locally finite infinite-upper-end case.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {x : ℝ≥0 → ℝ}

theorem IsCadlagPath.boundedVariationOn_Icc_of_Ioo (hx : IsCadlagPath x)
    {a b : ℝ≥0} (hab : a < b) (hv : BoundedVariationOn x (Ioo a b)) :
    BoundedVariationOn x (Icc a b) := by
  obtain ⟨l, hl⟩ := hx.2 b (ne_of_gt (bot_le.trans_lt hab))
  have hne : (𝓝[Ioi a ∩ Iio b] b).NeBot := by
    change (𝓝[Ioo a b] b).NeBot
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact nhdsLT_neBot_of_exists_lt ⟨a, hab⟩
  have heq := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist hne
    (show b ∈ Ioi a from hab) (hl.mono_left (nhdsWithin_mono b inter_subset_right))
  change eVariationOn x (Ioc a b) = eVariationOn x (Ioo a b) + edist (x b) l at heq
  change eVariationOn x (Icc a b) ≠ ⊤
  rw [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt (hx.1 a), heq]
  exact ENNReal.add_ne_top.mpr ⟨hv, edist_ne_top _ _⟩

theorem IsCadlagPath.boundedVariationOn_stopped_increment (hx : IsCadlagPath x)
    {a b : ℝ≥0} (hab : a < b) (hv : BoundedVariationOn x (Ioo a b)) :
    BoundedVariationOn (fun t ↦ x (min t b) - x (min t a)) univ := by
  have hclosed := hx.boundedVariationOn_Icc_of_Ioo hab hv
  have hclamp : BoundedVariationOn (fun t ↦ x (min (max t a) b)) univ := by
    apply ne_top_of_le_ne_top hclosed
    exact eVariationOn.comp_le_of_monotoneOn x (s := Icc a b) (t := univ)
      (fun t ↦ min (max t a) b)
      (fun _ _ _ _ h ↦ min_le_min_right b (max_le_max_right a h))
      (fun t _ ↦ ⟨le_min (le_max_right t a) hab.le, min_le_right _ _⟩)
  have hconst : BoundedVariationOn (fun _ : ℝ≥0 ↦ x a) univ :=
    (monotone_const.monotoneOn univ).boundedVariationOn (C := |x a|) (fun _ _ ↦ le_rfl)
  have heq : (fun t ↦ x (min t b) - x (min t a)) =
      fun t ↦ x (min (max t a) b) - x a := by
    funext t
    by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left (hta.trans hab.le), max_eq_right hta,
        min_eq_left hab.le, sub_self, sub_self]
    · rw [min_eq_right (le_of_not_ge hta), max_eq_left (le_of_not_ge hta)]
  rw [heq]
  exact boundedVariationOn_sub hclamp hconst

theorem IsCadlagPath.locallyBoundedVariationOn_after (hx : IsCadlagPath x) (a : ℝ≥0)
    (hv : ∀ b : ℝ≥0, BoundedVariationOn x (Ioo a b)) :
    LocallyBoundedVariationOn (fun t ↦ x t - x (min t a)) univ := by
  intro c d _ _
  change eVariationOn (fun t ↦ x t - x (min t a)) (univ ∩ Icc c d) ≠ ⊤
  by_cases hda : d ≤ a
  · have heq : EqOn (fun t ↦ x t - x (min t a)) (fun _ ↦ (0 : ℝ)) (univ ∩ Icc c d) := by
      intro t ht
      change x t - x (min t a) = 0
      rw [min_eq_left (ht.2.2.trans hda), sub_self]
    rw [eVariationOn.congr heq]
    exact ((monotone_const.monotoneOn univ).boundedVariationOn
      (C := (0 : ℝ)) (fun _ _ ↦ by simp)).mono inter_subset_left
  · have heq : EqOn (fun t ↦ x t - x (min t a))
        (fun t ↦ x (min t d) - x (min t a)) (univ ∩ Icc c d) := by
      intro t ht
      change x t - x (min t a) = x (min t d) - x (min t a)
      rw [min_eq_left ht.2.2]
    rw [eVariationOn.congr heq]
    exact (hx.boundedVariationOn_stopped_increment (lt_of_not_ge hda) (hv d)).mono inter_subset_left

theorem locallyBoundedVariationOn_stopped_difference_of_interval
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hx : IsCadlagPath (X · ω)) (hστ : σ ω < τ ω)
    (hv : ∀ b : ℝ≥0, (b : WithTop ℝ≥0) ≤ τ ω →
      BoundedVariationOn (X · ω) (Ioo (σ ω).untopA b)) :
    LocallyBoundedVariationOn
      (fun t ↦ stoppedProcess X τ t ω - stoppedProcess X σ t ω) univ := by
  cases hσ : σ ω with
  | top => simp only [hσ, not_top_lt] at hστ
  | coe a =>
    cases hτ : τ ω with
    | top =>
      have hv' (b : ℝ≥0) : BoundedVariationOn (X · ω) (Ioo a b) := by
        simpa only [hσ, WithTop.untopA, WithTop.untopD_coe] using
          hv b (by rw [hτ]; exact le_top)
      simpa only [stoppedProcess, hτ, hσ, min_eq_left le_top, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using hx.locallyBoundedVariationOn_after a hv'
    | coe b =>
      have hab : a < b := WithTop.coe_lt_coe.mp (by simpa only [hσ, hτ] using hστ)
      have hv' : BoundedVariationOn (X · ω) (Ioo a b) := by
        simpa only [hσ, WithTop.untopA, WithTop.untopD_coe] using hv b (by rw [hτ])
      have hb := (hx.boundedVariationOn_stopped_increment hab hv').locallyBoundedVariationOn
      simpa only [stoppedProcess, hτ, hσ, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using hb

end ProbabilityTheory
