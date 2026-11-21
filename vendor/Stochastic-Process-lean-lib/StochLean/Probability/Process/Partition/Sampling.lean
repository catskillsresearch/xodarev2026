/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousReindex
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousTerminalLp
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def pointNat (π : StoppingTimePartition F) (n : ℕ) : FiniteStoppingTime F :=
  π.point ⟨min n π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem pointNat_fin (π : StoppingTimePartition F) (i : Fin (π.size + 1)) :
    π.pointNat i = π.point i := by
  simp only [pointNat, min_eq_left (Nat.le_of_lt_succ i.isLt)]

theorem pointNat_mono (π : StoppingTimePartition F) (ω : Ω) :
    Monotone (fun n ↦ π.pointNat n ω) := by
  intro n m hnm
  exact π.monotone_point ω (show min n π.size ≤ min m π.size from min_le_min_right _ hnm)

theorem pointNat_withTop_mono (π : StoppingTimePartition F) :
    Monotone (fun n ↦ (π.pointNat n).withTop) := by
  intro n m hnm ω
  exact WithTop.coe_le_coe.mpr (π.pointNat_mono ω hnm)

@[simp] theorem pointNat_zero (π : StoppingTimePartition F) (ω : Ω) : π.pointNat 0 ω = 0 :=
  π.first_eq_zero ω

@[instance_reducible]
def sampledFiltration (π : StoppingTimePartition F) : Filtration ℕ mΩ :=
  F.stoppingTimeReindex (fun n ↦ (π.pointNat n).withTop)
    (fun n ↦ (π.pointNat n).isStoppingTime) π.pointNat_withTop_mono

@[simp] theorem sampledFiltration_apply (π : StoppingTimePartition F) (n : ℕ) :
    π.sampledFiltration n = (π.pointNat n).measurableSpace := rfl

theorem zero_le_sampledFiltration (π : StoppingTimePartition F) (n : ℕ) :
    F 0 ≤ π.sampledFiltration n :=
  (π.pointNat n).isStoppingTime.le_measurableSpace_of_const_le (fun _ ↦ bot_le)

def sampledProcess {E : Type*} (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → E) :
    ℕ → Ω → E := fun n ω ↦ X (π.pointNat n ω) ω

@[simp] theorem sampledProcess_zero {E : Type*} (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → E) : π.sampledProcess X 0 = X 0 := by
  funext ω
  simp only [sampledProcess, pointNat_zero]

@[simp] theorem sampledProcess_size {E : Type*} (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → E) : π.sampledProcess X π.size = fun ω ↦ X (π.terminal ω) ω := by
  funext ω
  change X (π.pointNat π.size ω) ω = X (π.point (Fin.last π.size) ω) ω
  exact congrArg (fun τ : FiniteStoppingTime F ↦ X (τ ω) ω)
    (π.pointNat_fin (Fin.last π.size))

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem martingale_sampledProcess_of_ui (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Martingale (π.sampledProcess X) π.sampledFiltration P := by
  exact hX.stoppingTimeReindex_of_ae_finite_usual hu hF hr
    (fun n ↦ (π.pointNat n).withTop) (fun n ↦ (π.pointNat n).isStoppingTime)
    π.pointNat_withTop_mono (fun n ↦ ae_of_all _ (π.pointNat n).withTop_ne_top)

variable [SigmaFiniteFiltration P F]

theorem martingale_sampledProcess_min_const (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) (T : ℝ≥0) :
    Martingale (π.sampledProcess (fun t ↦ X (min t T))) π.sampledFiltration P :=
  π.martingale_sampledProcess_of_ui (hX.isUIMartingale_min_const T).1
    (hX.isUIMartingale_min_const T).2 hF (hr.mono (fun _ h ↦ h.min_const T))

theorem memLp_sampledProcess_min_const (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hXT : MemLp (X T) p P) (n : ℕ) :
    MemLp (π.sampledProcess (fun t ↦ X (min t T)) n) p P :=
  hX.memLp_finiteStoppingTime_min hF hr (π.pointNat n) T hp hXT

end ProbabilityTheory.StoppingTimePartition
