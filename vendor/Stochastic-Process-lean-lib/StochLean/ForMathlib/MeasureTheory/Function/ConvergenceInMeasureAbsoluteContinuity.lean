/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Convergence in measure under an absolutely continuous finite measure -/

@[expose] public section

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
  {P Q : Measure Ω} [IsFiniteMeasure Q] {f : ℕ → Ω → E} {g : Ω → E}

theorem TendstoInMeasure.absolutelyContinuous (h : TendstoInMeasure P f atTop g)
    (hQP : Q ≪ P) (hf : ∀ n, AEStronglyMeasurable (f n) P) :
    TendstoInMeasure Q f atTop g := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n ↦ (hf n).mono_ac hQP)).mpr
  intro ns hns
  obtain ⟨ms, hms, hm⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ms, hms, hQP.ae_le hm⟩

end MeasureTheory
