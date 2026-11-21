/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import StochLean.Probability.Martingale.Doob.ConditionalEnvelope
public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import Mathlib.Probability.Process.Stopping

/-! # Random stopping reduces global conditional moduli to compact ones

If a bounded adapted process is constant after a stopping time, its global
conditional increment modulus is controlled by a compact modulus and the
maximal conditional probability that the stopping time exceeds the compact
horizon. The stopping time need not be almost surely finite for this bridge.

Every comparison is first proved for a fixed pair of times and then lifted
through essential-supremum minimality. The original bound proves both moduli
finite, and the tail indicator bound proves the running supremum finite,
before any of their real values are used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
  {T δ : ℝ≥0} {G W : Ω → ℝ≥0∞} {N : ℝ}

/-- An actual stopping-time tail controls the difference between a global and
a compact conditional modulus. No right-continuity of the original process
or filtration, or finiteness of the stopping time, is required here. -/
theorem IsGlobalConditionalIncrementModulus.ae_bounds_of_stopping_time
    (hG : IsGlobalConditionalIncrementModulus F P X δ G)
    (hW : IsConditionalIncrementModulus F P X T δ W)
    (hX : Adapted F X) (hτ : IsStoppingTime F τ)
    (hstop : ∀ᵐ ω ∂P, ∀ t u : ℝ≥0,
      τ ω ≤ (t : WithTop ℝ≥0) → t ≤ u → X t ω = X u ω)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (M : ℝ≥0 → Ω → ℝ) (hrM : HasRightContinuousPaths M P)
    (heM : ∀ t : ℝ≥0, M t =ᵐ[P]
      P[{ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P, G ω ≠ ∞ ∧ W ω ≠ ∞ ∧ denseRunningSupremum M T ω ≠ ∞ ∧
      G ω ≤ ENNReal.ofReal ((W ω).toReal +
        2 * N * (denseRunningSupremum M T ω).toReal) ∧
      (G ω).toReal ≤ (W ω).toReal +
        2 * N * (denseRunningSupremum M T ω).toReal := by
  classical
  let I : Ω → ℝ := {ω | (T : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ (1 : ℝ))
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hiX (t : ℝ≥0) : Integrable (X t) P := by
    have hp : MemLp (X t) 1 P := MemLp.of_bound
      ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t)
    exact hp.integrable le_rfl
  have hiI : Integrable I P := (integrable_const (1 : ℝ)).indicator
    (F.le T _ (hτ.measurableSet_gt T))
  have hIle : ∀ᵐ ω ∂P, I ω ≤ 1 := Eventually.of_forall fun ω ↦
    indicator_le_self' (fun _ _ ↦ zero_le_one) ω
  have heI (t : ℝ≥0) (hTt : T ≤ t) : P[I | F t] = I :=
    condExp_of_stronglyMeasurable (F.le t)
      (stronglyMeasurable_const.indicator
        (F.mono hTt _ (hτ.measurableSet_gt T))) hiI
  have hMcap : ∀ᵐ ω ∂P, denseRunningSupremum M T ω ≤ ENNReal.ofReal 1 := by
    apply ae_denseRunningSupremum_le_of_ae_le
    intro t _
    filter_upwards [heM t,
      condExp_le_nonneg_const (m := F t) (by norm_num : (0 : ℝ) ≤ 1) hIle]
      with ω he hle
    exact he.le.trans hle
  have hMfin : ∀ᵐ ω ∂P, denseRunningSupremum M T ω ≠ ∞ :=
    hMcap.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hWfin : ∀ᵐ ω ∂P, W ω ≠ ∞ := hW.ae_ne_top_of_norm_bound
    (fun t _ ↦ hiX t) (fun t _ ↦ hbound.mono fun _ hω ↦ hω t)
  have hGfin : ∀ᵐ ω ∂P, G ω ≠ ∞ := hG.ae_ne_top_of_norm_bound hiX
    (fun t ↦ hbound.mono fun _ hω ↦ hω t)
  have htail (v u s : ℝ≥0) (hTv : T ≤ v) (hvu : v ≤ u) :
      P[X v - X u | F s] ≤ᵐ[P] (fun ω ↦ 2 * N * P[I | F s] ω) := by
    have hp : X v - X u ≤ᵐ[P] (2 * N) • I := by
      filter_upwards [hbound, hstop] with ω hb hs
      change X v ω - X u ω ≤ 2 * N * I ω
      by_cases hbad : (T : WithTop ℝ≥0) < τ ω
      · have hiω : I ω = 1 :=
          indicator_of_mem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hbad (fun _ ↦ (1 : ℝ))
        rw [hiω, mul_one]
        have hn := (norm_sub_le (X v ω) (X u ω)).trans (add_le_add (hb v) (hb u))
        have hl : X v ω - X u ω ≤ ‖X v ω - X u ω‖ := by
          simpa only [Real.norm_eq_abs] using le_abs_self (X v ω - X u ω)
        linarith
      · have hiω : I ω = 0 :=
          indicator_of_notMem (s := {ω | (T : WithTop ℝ≥0) < τ ω}) hbad (fun _ ↦ (1 : ℝ))
        have hτv : τ ω ≤ (v : WithTop ℝ≥0) :=
          (le_of_not_gt hbad).trans (WithTop.coe_le_coe.mpr hTv)
        rw [hiω, hs v u hτv hvu, sub_self, mul_zero]
    have hm := condExp_mono (m := F s) ((hiX v).sub (hiX u)) (hiI.smul (2 * N)) hp
    have he := condExp_smul (2 * N) I (F s) (μ := P)
    filter_upwards [hm, he] with ω hmω heω
    exact hmω.trans_eq heω
  have hsup : G ≤ᵐ[P] (fun ω ↦ ENNReal.ofReal ((W ω).toReal +
      2 * N * (denseRunningSupremum M T ω).toReal)) := by
    apply hG.ae_le_of_bound
    intro t u htu huδ
    by_cases huT : u ≤ T
    · have hw := hW.conditional_increment_le htu huT huδ
      filter_upwards [hw, hWfin] with ω hwω hfω
      apply ENNReal.ofReal_le_ofReal
      exact ((ENNReal.ofReal_le_iff_le_toReal hfω).mp hwω).trans
        (le_add_of_nonneg_right (mul_nonneg hC ENNReal.toReal_nonneg))
    · have hTu : T ≤ u := (lt_of_not_ge huT).le
      by_cases htT : t ≤ T
      · have hw := hW.conditional_increment_le htT le_rfl (hTu.trans huδ)
        have hr := htail T u t le_rfl hTu
        have hadd := condExp_add ((hiX t).sub (hiX T)) ((hiX T).sub (hiX u)) (F t)
        have hdiff : (X t - X T) + (X T - X u) = X t - X u := by
          funext ω
          change (X t ω - X T ω) + (X T ω - X u ω) = X t ω - X u ω
          ring
        rw [hdiff] at hadd
        filter_upwards [hw, hr, hadd, heM t, hWfin, hrM, hMfin]
          with ω hwω hrω haω heω hfω hcω hmω
        apply ENNReal.ofReal_le_ofReal
        have hMsup := le_toReal_denseRunningSupremum_of_rightContinuous htT hcω hmω
        have hMbound : P[I | F t] ω ≤ (denseRunningSupremum M T ω).toReal := by
          change M t ω = P[I | F t] ω at heω
          exact heω.symm.le.trans hMsup
        have hsmall := (ENNReal.ofReal_le_iff_le_toReal hfω).mp hwω
        have hrest := hrω.trans (mul_le_mul_of_nonneg_left hMbound hC)
        exact haω.le.trans (add_le_add hsmall hrest)
      · have hTt : T ≤ t := (lt_of_not_ge htT).le
        have hr := htail t u t hTt htu
        have hIT : M T =ᵐ[P] I := by
          have he := heM T
          change M T =ᵐ[P] P[I | F T] at he
          rw [heI T le_rfl] at he
          exact he
        rw [heI t hTt] at hr
        filter_upwards [hr, hIT, hrM, hMfin] with ω hrω heω hcω hmω
        apply ENNReal.ofReal_le_ofReal
        have hIsup : I ω ≤ (denseRunningSupremum M T ω).toReal :=
          heω.symm.le.trans
            (le_toReal_denseRunningSupremum_of_rightContinuous le_rfl hcω hmω)
        exact (hrω.trans (mul_le_mul_of_nonneg_left hIsup hC)).trans
          (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  filter_upwards [hGfin, hWfin, hMfin, hsup] with ω hgω hwω hmω hsω
  refine ⟨hgω, hwω, hmω, hsω, ?_⟩
  have hnonneg : 0 ≤ (W ω).toReal + 2 * N * (denseRunningSupremum M T ω).toReal :=
    add_nonneg ENNReal.toReal_nonneg (mul_nonneg hC ENNReal.toReal_nonneg)
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    (ENNReal.toReal_le_toReal hgω ENNReal.ofReal_ne_top).mpr hsω

end ProbabilityTheory
