/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ShiftedConditionalSupermartingale
public import StochLean.Probability.Martingale.Doob.ShiftedConditionalModulusOrder
public import StochLean.Probability.Process.Path.Subtraction

/-! # Coherent decreasing signed conditional residuals

Actual cadlag shifted projections are constructed first. Their countably
many bound and adjacent-order events, together with the original input's
cadlag event, are combined into one full-measure event in the initial field.
Resetting its complement gives everywhere cadlag, nonnegative, bounded and
ordered residuals. No proposed sequence or convergence conclusion is assumed.

All coordinate and bounded stopping identities concern the original input,
not merely an auxiliary regular version. The endpoint at time zero is kept.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The true shifted conditional projections produce a coherent signed
residual sequence suitable for comparing actual first-hitting times. -/
theorem Supermartingale.exists_coherent_conditional_residuals_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C)
    (δ : ℕ → ℝ≥0) (hδ : Antitone δ) :
    ∃ R : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, StronglyAdapted F (R n)) ∧
      (∀ n ω, IsCadlagPath (R n · ω)) ∧
      (∀ n ω t, 0 ≤ R n t ω ∧ R n t ω ≤ 2 * C) ∧
      (∀ t ω, Antitone (fun n ↦ R n t ω)) ∧
      (∀ n t, R n t =ᵐ[P] X t - P[X (t + δ n) | F t]) ∧
      ∀ (n : ℕ) (σ : FiniteStoppingTime F) (T : ℝ≥0), (∀ ω, σ ω ≤ T) →
        (fun ω ↦ R n (σ ω) ω) =ᵐ[P]
          (fun ω ↦ X (σ ω) ω) - P[(fun ω ↦ X (σ ω + δ n) ω) | σ.measurableSpace] := by
  classical
  choose Q hQ hcQ heQ hbQ hsQ using fun n ↦
    hX.exists_cadlag_condExp_add_time_of_bound hF hc hb (δ n)
  have hord (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, Q n t ω ≤ Q (n + 1) t ω :=
    hX.ae_forall_condExp_add_time_le_of_le (hδ (Nat.le_succ n))
      (Eventually.of_forall fun ω ↦ (hcQ (n + 1) ω).1)
      (Eventually.of_forall fun ω ↦ (hcQ n ω).1) (heQ (n + 1)) (heQ n)
  let G : Set Ω := {ω | IsCadlagPath (X · ω) ∧ (∀ t, ‖X t ω‖ ≤ C) ∧
    (∀ n t, ‖Q n t ω‖ ≤ C ∧ Q n t ω ≤ X t ω) ∧
      ∀ n t, Q n t ω ≤ Q (n + 1) t ω}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hc, hb, ae_all_iff.mpr hbQ, ae_all_iff.mpr hord] with ω hcω hbω hQω hoω
    exact ⟨hcω, hbω, hQω, hoω⟩
  have hG : MeasurableSet[F 0] G := by
    have hGc : MeasurableSet[F 0] Gᶜ := hF.complete_initial _ (ae_iff.mp hGae)
    simpa only [compl_compl] using hGc.compl
  let R : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦ if ω ∈ G then X t ω - Q n t ω else 0
  have heR (n : ℕ) : Indistinguishable (R n) (X - Q n) P := by
    filter_upwards [hGae] with ω hω t
    exact if_pos hω
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t
    exact StronglyMeasurable.ite (F.mono bot_le _ hG)
      ((hX.stronglyAdapted t).sub ((hQ n).stronglyAdapted t)) stronglyMeasurable_const
  · intro n ω
    by_cases hω : ω ∈ G
    · have hh := hω.1.sub (hcQ n ω)
      change IsCadlagPath (fun t ↦ X t ω - Q n t ω) at hh
      simpa only [R, if_pos hω] using hh
    · simp only [R, if_neg hω]
      exact IsContinuousPath.isCadlagPath continuous_const
  · intro n ω t
    by_cases hω : ω ∈ G
    · simp only [R, if_pos hω]
      have hx := abs_le.mp (by simpa only [Real.norm_eq_abs] using hω.2.1 t)
      have hq := abs_le.mp (by simpa only [Real.norm_eq_abs] using (hω.2.2.1 n t).1)
      exact ⟨sub_nonneg.mpr (hω.2.2.1 n t).2, by linarith only [hx.2, hq.1]⟩
    · simp only [R, if_neg hω, le_refl, true_and]
      positivity
  · intro t ω
    apply antitone_nat_of_succ_le
    intro n
    by_cases hω : ω ∈ G
    · simp only [R, if_pos hω]
      exact sub_le_sub_left (hω.2.2.2 n t) _
    · simp only [R, if_neg hω, le_refl]
  · intro n t
    filter_upwards [(heR n).ae_eq t, heQ n t] with ω hRω hQω
    change R n t ω = X t ω - P[X (t + δ n) | F t] ω
    exact hRω.trans (congrArg (fun a ↦ X t ω - a) hQω)
  · intro n σ T hσ
    filter_upwards [heR n, hsQ n σ T hσ] with ω hRω hQω
    change R n (σ ω) ω = X (σ ω) ω -
      P[(fun ω ↦ X (σ ω + δ n) ω) | σ.measurableSpace] ω
    exact (hRω (σ ω)).trans (congrArg (fun a ↦ X (σ ω) ω - a) hQω)

end MeasureTheory
