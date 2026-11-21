/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale
public import StochLean.Probability.Process.ClassD.Basic
public import StochLean.Probability.Martingale.Convergence.InMeasure

/-! # Class D local martingales

A Protter local martingale whose finite stopping values form a uniformly
integrable family is a true uniformly integrable martingale.  The proof uses
the native masked-to-unmasked localization bridge; no unrecorded replacement
of the project's local-martingale predicate is made.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

/-- A Class D Protter local martingale is a true uniformly integrable martingale. -/
theorem IsLocalMartingale.isUIMartingale_of_classD
    (hX : IsLocalMartingale X F P) (hD : IsClassD X F P) :
    IsUIMartingale X F P := by
  obtain ⟨τ, hτ⟩ := hX.exists_klenkeLocalizingSequence (hD.integrable 0)
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess X (τ n)
  have hYm (n : ℕ) : Martingale (Y n) F P := (hτ.2.2 n).1
  have hYui (t : ℝ≥0) : UniformIntegrable (fun n ↦ Y n t) 1 P := by
    let σ : ℕ → FiniteStoppingTime F := fun n ↦
      FiniteStoppingTime.truncate (hτ.1.isStoppingTime n) t
    have hui := hD.uniformIntegrable_finiteStoppingTime σ
    exact hui.ae_eq fun n ↦ ae_of_all P fun ω ↦ by
      change X (σ n ω) ω = stoppedProcess X (τ n) t ω
      exact congrFun (FiniteStoppingTime.stoppedValue_truncate X
        (hτ.1.isStoppingTime n) t) ω
  have hYlim (t : ℝ≥0) : TendstoInMeasure P (fun n ↦ Y n t) atTop (X t) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hYm n).integrable t).aestronglyMeasurable)
    filter_upwards [hτ.1.tendsto_top] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))] with n hn
    exact (stoppedProcess_eq_of_le hn.le).symm
  exact ⟨martingale_of_tendstoInMeasure_uniformIntegrable hYm hX.1.stronglyAdapted
    hYui hYlim, hD.uniformIntegrable⟩

end ProbabilityTheory
