/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.UniformUCP
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.FirstExitTruncation

/-! # UCP continuity of the source elementary integral process

Protter II.11 on the full simple predictable source class. Actual left-continuous
first-exit truncations are uniformly bounded and agree with the source before the
exit. A slightly larger input horizon avoids attributing an open hit to its boundary,
including a right jump at time zero. No density, completeness or limit selector is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.elementaryIntegralProcess_ucp_bound
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (T S : ℝ≥0) (hTS : T < S) (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤
        η + P {ω | ∃ t ≤ S, δ < ‖H t ω‖} := by
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegralProcess_maximal_uniform hF T ε hε η hη
  refine ⟨δ, hδ, fun H hH ↦ ?_⟩
  let τ := hittingAfter H {x | δ < ‖x‖} 0
  have hmax := hb (firstExitTruncation H δ) (hH.firstExitTruncation δ)
    (hH.norm_firstExitTruncation_le hδ.le)
  have hbad : P {ω | τ ω ≤ (T : WithTop ℝ≥0)} ≤ P {ω | ∃ t ≤ S, δ < ‖H t ω‖} := by
    apply measure_mono
    intro ω hω
    have hlt : τ ω < (S : WithTop ℝ≥0) := hω.trans_lt (WithTop.coe_lt_coe.mpr hTS)
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp hlt
    exact ⟨t, ht.2.le, hhit⟩
  have hsub : {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ⊆
      {ω | ∃ t ≤ T, ε < ‖(hH.firstExitTruncation δ).elementaryIntegralProcess X t ω‖} ∪
        {ω | τ ω ≤ (T : WithTop ℝ≥0)} := by
    rintro ω ⟨t, ht, hω⟩
    by_cases hτ : τ ω ≤ (T : WithTop ℝ≥0)
    · exact Or.inr hτ
    · refine Or.inl ⟨t, ht, ?_⟩
      rw [hH.elementaryIntegralProcess_firstExitTruncation_eq_of_lt δ X
        ((WithTop.coe_le_coe.mpr ht).trans_lt (lt_of_not_ge hτ))]
      exact hω
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hmax hbad))

theorem IsSemimartingale.tendstoUCP_elementaryIntegralProcess_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} (hH : ∀ n, IsSimplePredictable (H n) F)
    (hu : TendstoUCP P H atTop 0) :
    TendstoUCP P (fun n ↦ (hH n).elementaryIntegralProcess X) atTop 0 := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  simp only [Pi.zero_apply, sub_zero]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegralProcess_ucp_bound hF T (T + 1)
    (lt_add_one T) ε hε (η / 2) (ENNReal.half_pos hη.ne')
  have hin := tendstoUCP_iff_measure_exists_norm_lt.mp hu (T + 1) δ hδ
  simp only [Pi.zero_apply, sub_zero] at hin
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hin (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    _ ≤ η / 2 + P {ω | ∃ t ≤ T + 1, δ < ‖H n t ω‖} := hb (H n) (hH n)
    _ ≤ η / 2 + η / 2 := add_le_add le_rfl (hN n hn)
    _ = η := ENNReal.add_halves η

/-- Protter II.11: the source elementary integral operator is continuous from S_UCP to D_UCP. -/
theorem IsSemimartingale.tendstoUCP_elementaryIntegralProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} {K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ n, IsSimplePredictable (H n) F) (hK : IsSimplePredictable K F)
    (hu : TendstoUCP P H atTop K) :
    TendstoUCP P (fun n ↦ (hH n).elementaryIntegralProcess X) atTop
      (hK.elementaryIntegralProcess X) := by
  have hd : TendstoUCP P (fun n t ω ↦ H n t ω - K t ω) atTop 0 := by
    apply tendstoUCP_iff_measure_exists_norm_lt.mpr
    intro T ε hε
    simpa only [Pi.zero_apply, sub_zero] using
      tendstoUCP_iff_measure_exists_norm_lt.mp hu T ε hε
  have hj := hX.tendstoUCP_elementaryIntegralProcess_zero hF (fun n ↦ (hH n).sub hK) hd
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have heq (n : ℕ) := (hH n).elementaryIntegralProcess_sub hK X
  have h := tendstoUCP_iff_measure_exists_norm_lt.mp hj T ε hε
  simpa only [heq, Pi.sub_apply, Pi.zero_apply, sub_zero] using h

/-- Uniform control of differences also sends UCP-Cauchy simple inputs to UCP-Cauchy outputs.
This supplies a Cauchy estimate, not an assumed complete space or a selected limit. -/
theorem IsSemimartingale.elementaryIntegralProcess_cauchyUCP
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} (hH : ∀ n, IsSimplePredictable (H n) F)
    (hc : ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n → P {ω | ∃ t ≤ T, ε < ‖H m t ω - H n t ω‖} ≤ η) :
    ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n → P {ω | ∃ t ≤ T,
        ε < ‖(hH m).elementaryIntegralProcess X t ω -
          (hH n).elementaryIntegralProcess X t ω‖} ≤ η := by
  intro T ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegralProcess_ucp_bound hF T (T + 1)
    (lt_add_one T) ε hε (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨N, hN⟩ := hc (T + 1) δ hδ (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  have h := hb (H m - H n) ((hH m).sub (hH n))
  rw [(hH m).elementaryIntegralProcess_sub (hH n) X] at h
  exact h.trans ((add_le_add le_rfl (hN m n hm hn)).trans (ENNReal.add_halves η).le)

end ProbabilityTheory
