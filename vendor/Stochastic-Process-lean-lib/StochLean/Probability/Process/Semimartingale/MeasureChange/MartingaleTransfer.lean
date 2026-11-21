/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.EquivalentDensityLocalization
public import StochLean.Probability.Martingale.Convergence.ContinuousClosure

/-! # Martingale transfer by an equivalent density

If `Q` and `P` are equivalent and `Z` is the canonical density process of
`Q` with respect to `P`, every `Q`-martingale `X` gives a `P`-martingale
`Z * X`.  Uniform integrability transfers as well.  The proofs use the
division-free Bayes identity and an actual integrable closing variable.

Local martingales are transferred by stopping the already transferred UI
martingales along the original fundamental sequence.  This file does not yet
state the Girsanov--Meyer covariation correction.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace MeasureTheory.Martingale

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Multiplication by the canonical density transfers true martingales from
the target law to the source law under equivalence. -/
theorem mul_densityProcess_of_equivalent
    (hX : Martingale X F Q) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    Martingale (densityProcess Q P F * X) F P := by
  have hZ : Martingale (densityProcess Q P F) F P := martingale_densityProcess hF
  refine ⟨hZ.stronglyAdapted.mul hX.stronglyAdapted, ?_⟩
  intro s t hst
  change P[(fun ω ↦ densityProcess Q P F t ω * X t ω) | F s] =ᵐ[P]
    fun ω ↦ densityProcess Q P F s ω * X s ω
  have hXt : Integrable (X t) Q := hX.integrable t
  have hself_t : Q[X t | F t] =ᵐ[Q] X t :=
    Eventually.of_forall fun ω ↦ congrFun
      (condExp_of_stronglyMeasurable (F.le t) (hX.stronglyAdapted t) hXt) ω
  have hproduct_t :
      (fun ω ↦ densityProcess Q P F t ω * X t ω) =ᵐ[P]
        P[fun ω ↦ terminalDensity Q P ω * X t ω | F t] := by
    filter_upwards [densityProcess_mul_condExp_ae_eq hQP hF hXt t,
        hPQ.ae_le hself_t]
      with ω hbayes hself
    rw [← hself]
    exact hbayes
  calc
    P[(fun ω ↦ densityProcess Q P F t ω * X t ω) | F s] =ᵐ[P]
        P[P[fun ω ↦ terminalDensity Q P ω * X t ω | F t] | F s] :=
      condExp_congr_ae hproduct_t
    _ =ᵐ[P] P[fun ω ↦ terminalDensity Q P ω * X t ω | F s] :=
      condExp_condExp_of_le (F.mono hst) (F.le t)
    _ =ᵐ[P] (fun ω ↦ densityProcess Q P F s ω * Q[X t | F s] ω) :=
      (densityProcess_mul_condExp_ae_eq hQP hF hXt s).symm
    _ =ᵐ[P] (fun ω ↦ densityProcess Q P F s ω * X s ω) := by
      filter_upwards [hPQ.ae_le (hX.condExp_ae_eq hst)] with ω hω
      rw [hω]

end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Multiplication by the canonical density transfers uniformly integrable
martingales from the target law to the source law under equivalence. -/
theorem IsUIMartingale.mul_densityProcess_of_equivalent
    (hX : IsUIMartingale X F Q) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    IsUIMartingale (densityProcess Q P F * X) F P := by
  refine ⟨MeasureTheory.Martingale.mul_densityProcess_of_equivalent
    hX.1 hQP hPQ hF, ?_⟩
  obtain ⟨Y, hY, hclose⟩ := hX.1.exists_integrable_closing hX.2
  have hDY : Integrable (fun ω ↦ terminalDensity Q P ω * Y ω) P := by
    simpa only [terminalDensity] using
      (integrable_toReal_rnDeriv_mul_iff hQP).2 hY
  apply MeasureTheory.Martingale.uniformIntegrable_of_integrable_closing hDY
  intro t
  filter_upwards [densityProcess_mul_condExp_ae_eq hQP hF hY t,
      hPQ.ae_le (hclose t)]
    with ω hbayes hω
  change densityProcess Q P F t ω * X t ω =
    P[fun x ↦ terminalDensity Q P x * Y x | F t] ω
  rw [hω]
  exact hbayes

/-- Multiplication by the canonical density transfers local martingales from
the target law to the source law under equivalence.  The original fundamental
sequence is retained; its convergence and the source càdlàg event are
transported through the reverse absolute continuity. -/
theorem IsLocalMartingale.mul_densityProcess_of_equivalent
    (hX : IsLocalMartingale X F Q) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    IsLocalMartingale (densityProcess Q P F * X) F P := by
  have hZ : Martingale (densityProcess Q P F) F P := martingale_densityProcess hF
  have hXcadP : HasCadlagPaths X P := hPQ.ae_le hX.2.1
  refine ⟨hZ.stronglyAdapted.adapted.mul hX.1,
    hasCadlagPaths_densityProcess.mul hXcadP, ?_⟩
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨τ, ⟨hτ.1.isStoppingTime, hPQ.ae_le hτ.1.tendsto_top⟩,
    hτ.2.1, fun n ↦ ?_⟩
  let Y : ℝ≥0 → Ω → ℝ :=
    stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hY : IsUIMartingale Y F Q := hτ.2.2 n
  have hYcadQ : HasCadlagPaths Y Q :=
    (hX.2.1.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)
  have hYcadP : HasCadlagPaths Y P := hPQ.ae_le hYcadQ
  have hZY : IsUIMartingale (densityProcess Q P F * Y) F P :=
    hY.mul_densityProcess_of_equivalent hQP hPQ hF
  have hstop := hZY.stoppedProcess_of_usual hF
    (hasCadlagPaths_densityProcess.mul hYcadP).hasRightContinuousPaths
    (hτ.1.isStoppingTime n)
  convert hstop using 1
  ext t ω
  by_cases hω : 0 < τ n ω
  · rw [stoppedProcess_indicator_comm,
      Set.indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hω)]
    rw [stoppedProcess_mul, stoppedProcess_mul]
    simp [Y, stoppedProcess_indicator_comm, hω]
  · simp [Y, stoppedProcess_indicator_comm, hω]

end ProbabilityTheory
