/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUniformIntegrable
public import StochLean.Probability.Process.Path.Algebra

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem IsUIMartingale.const_smul (hX : IsUIMartingale X F P) (c : ℝ) :
    IsUIMartingale (c • X) F P := by
  obtain ⟨Z, hi, hc⟩ := hX.1.exists_integrable_closing hX.2
  refine ⟨hX.1.smul c, MeasureTheory.Martingale.uniformIntegrable_of_integrable_closing (F := F)
    (hi.smul c) (fun t ↦ ?_)⟩
  exact ((hc t).const_smul c).trans (condExp_smul (μ := P) c Z (F t)).symm

theorem IsLocalMartingale.stoppedProcess (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) :
    IsLocalMartingale (MeasureTheory.stoppedProcess X σ) F P := by
  refine ⟨(hX.1.stronglyAdapted.stoppedProcess_of_usual hF hX.2.1.hasRightContinuousPaths
    hσ).adapted, hX.2.1.stoppedProcess σ, ?_⟩
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hr := ((hX.2.1.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)).hasRightContinuousPaths
  have hstop := (hτ.2.2 n).stoppedProcess_of_usual hF hr hσ
  simpa only [← stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess, inf_comm]
    using hstop

/-- Intersect a fundamental sequence with another increasing pre-localizer. -/
theorem IsFundamentalSequence.min_other {τ σ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsFundamentalSequence X F P τ) (hcad : HasCadlagPaths X P)
    (hF : F.IsUsual P) (hσ : IsPreLocalizingSequence F σ P) (hmono : Monotone σ) :
    IsFundamentalSequence X F P (min τ σ) := by
  refine ⟨⟨fun n ↦ (hτ.1.isStoppingTime n).min (hσ.isStoppingTime n), ?_⟩,
    hτ.2.1.inf hmono, fun n ↦ ?_⟩
  · filter_upwards [hτ.1.tendsto_top, hσ.tendsto_top] with ω hτω hσω
    simpa only [Pi.inf_apply, min_self] using hτω.min hσω
  · have hB : MeasurableSet[F 0] {ω | 0 < σ n ω} := by
      simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
        (hσ.isStoppingTime n 0).compl
    have hbase := (hτ.2.2 n).indicator_initial hB
    have hr := (((hcad.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)).indicator
      {ω | 0 < σ n ω}).hasRightContinuousPaths
    have hstop := hbase.stoppedProcess_of_usual hF hr (hσ.isStoppingTime n)
    convert hstop using 1
    simp_rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
    rw [← stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
    ext t ω
    simp only [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff,
      Set.ofPred_and, Set.inter_comm, inf_comm]

theorem IsLocalMartingale.add (hX : IsLocalMartingale X F P)
    (hY : IsLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsLocalMartingale (X + Y) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  obtain ⟨σ, hσ⟩ := hY.2.2
  have hx := hτ.min_other hX.2.1 hF hσ.1 hσ.2.1
  have hy := hσ.min_other hY.2.1 hF hτ.1 hτ.2.1
  rw [inf_comm σ τ] at hy
  refine ⟨hX.1.add hY.1, hX.2.1.add hY.2.1, min τ σ, hx.1, hx.2.1, fun n ↦ ?_⟩
  have hsum : IsUIMartingale
      ((MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < min τ σ n ω}.indicator (X t))
        (min τ σ n)) +
       (MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < min τ σ n ω}.indicator (Y t))
        (min τ σ n))) F P :=
      ⟨(hx.2.2 n).1.add (hy.2.2 n).1, (hx.2.2 n).2.add (hy.2.2 n).2 le_rfl⟩
  convert hsum using 1
  ext t ω
  rw [Pi.add_apply, Pi.add_apply, stoppedProcess_indicator_comm,
    stoppedProcess_indicator_comm, stoppedProcess_indicator_comm]
  simp only [stoppedProcess_add, Pi.add_apply, Set.indicator_add']

theorem IsLocalMartingale.const_smul (hX : IsLocalMartingale X F P) (c : ℝ) :
    IsLocalMartingale (c • X) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨(hX.1.stronglyAdapted.smul c).adapted, ?_, τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  · exact hX.2.1.continuous_comp
      (show Continuous (fun x : ℝ ↦ c * x) from continuous_const.mul continuous_id)
  · have heq : (fun t ↦ {ω | 0 < τ n ω}.indicator ((c • X) t)) =
        c • (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) := by
      funext t ω
      by_cases h : 0 < τ n ω <;> simp [h]
    rw [heq, stoppedProcess_const_smul]
    exact (hτ.2.2 n).const_smul c

theorem IsLocalMartingale.neg (hX : IsLocalMartingale X F P) :
    IsLocalMartingale (-X) F P := by simpa only [neg_one_smul] using hX.const_smul (-1)

theorem IsLocalMartingale.sub (hX : IsLocalMartingale X F P)
    (hY : IsLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsLocalMartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg hF

theorem IsContinuousLocalMartingale.stoppedProcess (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) :
    IsContinuousLocalMartingale (MeasureTheory.stoppedProcess X σ) F P :=
  ⟨hX.1.stoppedProcess hF hσ, hX.2.stoppedProcess σ⟩

end ProbabilityTheory
