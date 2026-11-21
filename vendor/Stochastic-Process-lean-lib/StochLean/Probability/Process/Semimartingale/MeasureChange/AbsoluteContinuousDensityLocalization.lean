/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.StoppingDensity
public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Process.Stopping.ThresholdHitting
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Localization before a density process becomes small

For probability measures `Q ≪ P`, the canonical density process need not be
strictly positive under `P`.  It is nevertheless positive under `Q` at every
finite stopping time.  We turn that fact into the localization used in
Protter III.41: stop when the density first enters the open interval below the
summable geometric threshold `2⁻⁽ⁿ⁺¹⁾`.

The stopped-density identity bounds the `Q`-probability of an exit before any
fixed horizon by the threshold.  Borel--Cantelli then proves that these exits
tend to infinity `Q`-almost surely.  Strictly before the exit, and hence for
positive left limits up to the exit, the density is bounded below by the same
threshold.  No equivalence assumption and no reverse density are used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- The summable positive threshold `2⁻⁽ⁿ⁺¹⁾` used to localize a
one-way density process away from zero. -/
noncomputable def absoluteContinuousDensityThreshold (n : ℕ) : ℝ≥0 :=
  1 / (2 : ℝ≥0) ^ (n + 1)

theorem absoluteContinuousDensityThreshold_pos (n : ℕ) :
    0 < absoluteContinuousDensityThreshold n := by
  simp only [absoluteContinuousDensityThreshold]
  positivity

theorem antitone_absoluteContinuousDensityThreshold :
    Antitone absoluteContinuousDensityThreshold := by
  intro n m hnm
  exact one_div_pow_anti (by norm_num : (1 : ℝ≥0) ≤ 2)
    (Nat.add_le_add_right hnm 1)

theorem summable_absoluteContinuousDensityThreshold :
    Summable absoluteContinuousDensityThreshold := by
  apply NNReal.summable_coe.mp
  apply (summable_geometric_two.mul_left ((1 : ℝ) / 2)).congr
  intro n
  simp only [absoluteContinuousDensityThreshold, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_pow, NNReal.coe_ofNat]
  rw [pow_succ']
  simp only [one_div]
  simpa only [inv_pow] using (mul_inv (2 : ℝ) (2 ^ n)).symm

/-- The geometric thresholds decrease to zero in the real topology. -/
theorem tendsto_absoluteContinuousDensityThreshold_zero :
    Tendsto (fun n : ℕ ↦ (absoluteContinuousDensityThreshold n : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp only [absoluteContinuousDensityThreshold, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_inv, one_div, inv_pow,
    Function.comp_apply]

/-- First entrance of the canonical density into the open interval below
`2⁻⁽ⁿ⁺¹⁾`.  An open set is essential: right-continuous adapted paths
then give a stopping time, while a finite hit is only known to lie in its
closure. -/
noncomputable def absoluteContinuousDensityExit (Q P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  hittingAfter (densityProcess Q P F)
    (Iio (absoluteContinuousDensityThreshold n : ℝ)) 0 ω

omit [IsProbabilityMeasure Q] in
/-- The density exits are stopping times in the usual source filtration. -/
theorem isStoppingTime_absoluteContinuousDensityExit
    (hF : F.IsUsual P) (n : ℕ) :
    IsStoppingTime F (absoluteContinuousDensityExit Q P F n) := by
  exact
    (martingale_densityProcess (Q := Q) hF).stronglyAdapted.adapted
      |>.isStoppingTime_hittingAfter_isOpen_of_usual hF
        (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)).hasRightContinuousPaths
        isOpen_Iio 0

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- Lower thresholds can only delay their first entrance. -/
theorem monotone_absoluteContinuousDensityExit (ω : Ω) :
    Monotone (fun n ↦ absoluteContinuousDensityExit Q P F n ω) := by
  intro n m hnm
  apply hittingAfter_anti (densityProcess Q P F) 0
  exact Iio_subset_Iio (antitone_absoluteContinuousDensityThreshold hnm)

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- Strictly before the exit, the density has not entered the open lower
interval and is therefore bounded below by the geometric threshold. -/
theorem absoluteContinuousDensityThreshold_le_of_lt_exit
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < absoluteContinuousDensityExit Q P F n ω) :
    (absoluteContinuousDensityThreshold n : ℝ) ≤ densityProcess Q P F t ω := by
  exact not_lt.mp
    (notMem_of_lt_hittingAfter (u := densityProcess Q P F)
      (s := Iio (absoluteContinuousDensityThreshold n : ℝ)) ht bot_le)

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- At a finite exit, right continuity gives the weak threshold inequality.
The open entrance condition itself must not be claimed at the hitting time. -/
theorem densityProcess_at_absoluteContinuousDensityExit_le
    {n : ℕ} {ω : Ω}
    (hpath : IsRightContinuousPath (densityProcess Q P F · ω))
    (hne : absoluteContinuousDensityExit Q P F n ω ≠ ⊤) :
    densityProcess Q P F
        (absoluteContinuousDensityExit Q P F n ω).untopA ω ≤
      (absoluteContinuousDensityThreshold n : ℝ) := by
  have hmem := hittingAfter_mem_closure_of_rightContinuous
    (X := densityProcess Q P F)
    (s := Iio (absoluteContinuousDensityThreshold n : ℝ)) hpath hne
  simpa only [absoluteContinuousDensityExit, closure_Iio, mem_Iic] using hmem

/-- The probability under `Q` of reaching the lower threshold before a fixed
horizon is at most that threshold. -/
theorem measure_absoluteContinuousDensityExit_le
    (hQP : Q ≪ P) (hF : F.IsUsual P) (n : ℕ) (T : ℝ≥0) :
    Q {ω | absoluteContinuousDensityExit Q P F n ω ≤ T} ≤
      (absoluteContinuousDensityThreshold n : ℝ≥0∞) := by
  let hR := isStoppingTime_absoluteContinuousDensityExit (Q := Q) hF n
  let τ := FiniteStoppingTime.truncate hR T
  let s : Set Ω := {ω | absoluteContinuousDensityExit Q P F n ω ≤ T}
  have hsτ : MeasurableSet[τ.measurableSpace] s :=
    FiniteStoppingTime.measurableSet_truncate_trigger hR T
  have hs : MeasurableSet s := τ.measurableSpace_le s hsτ
  have hreal : Q.real s ≤ (absoluteContinuousDensityThreshold n : ℝ) := by
    calc
      Q.real s = ∫ ω in s, densityProcess Q P F (τ ω) ω ∂P :=
        (setIntegral_densityProcess_sample hQP hF τ hsτ).symm
      _ ≤ ∫ _ω in s, (absoluteContinuousDensityThreshold n : ℝ) ∂P := by
        apply setIntegral_mono_on_ae
          (integrable_densityProcess_sample (Q := Q) hF τ).integrableOn
          (integrable_const (absoluteContinuousDensityThreshold n : ℝ)).integrableOn hs
        filter_upwards
            [hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)]
          with ω hω hωs
        have hRle : absoluteContinuousDensityExit Q P F n ω ≤ T := hωs
        rw [FiniteStoppingTime.truncate_eq_untopA_of_le hR hRle]
        exact densityProcess_at_absoluteContinuousDensityExit_le
          hω.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hRle)
      _ = P.real s * (absoluteContinuousDensityThreshold n : ℝ) := by
        rw [setIntegral_const, smul_eq_mul]
      _ ≤ (absoluteContinuousDensityThreshold n : ℝ) := by
        have hPnonneg : 0 ≤ P.real s := measureReal_nonneg
        have hPle : P.real s ≤ 1 := measureReal_le_one
        have hthreshold : 0 ≤ (absoluteContinuousDensityThreshold n : ℝ) :=
          (absoluteContinuousDensityThreshold_pos n).le
        nlinarith
  apply (ENNReal.toReal_le_toReal (measure_ne_top Q s) (by simp)).mp
  simpa only [measureReal_def, ENNReal.coe_toReal] using hreal

/-- The geometric lower-density exits tend to infinity under the target law.
This is the one-way substitute for the inverse-density localizer available
under equivalent measures. -/
theorem ae_tendsto_absoluteContinuousDensityExit
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂Q, Tendsto (fun n ↦ absoluteContinuousDensityExit Q P F n ω)
      atTop (𝓝 ⊤) := by
  have hthresholdSum :
      (∑' n : ℕ, (absoluteContinuousDensityThreshold n : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr
      summable_absoluteContinuousDensityThreshold
  have hsum (T : ℕ) :
      (∑' n : ℕ, Q {ω | absoluteContinuousDensityExit Q P F n ω ≤ (T : ℝ≥0)}) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b :=
      ∑' n : ℕ, (absoluteContinuousDensityThreshold n : ℝ≥0∞))
      hthresholdSum
    exact ENNReal.tsum_le_tsum fun n ↦
      measure_absoluteContinuousDensityExit_le hQP hF n T
  filter_upwards [ae_all_iff.mpr fun T : ℕ ↦ ae_eventually_notMem (hsum T)]
    with ω hω
  rw [WithTop.tendsto_nhds_top_iff]
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt t
  filter_upwards [hω T] with n hn
  have hnle : ¬ absoluteContinuousDensityExit Q P F n ω ≤ (T : ℝ≥0) := by
    simpa only [mem_ofPred_eq] using hn
  exact (WithTop.coe_lt_coe.mpr hT).trans (lt_of_not_ge hnle)

/-- The density exits form a genuine localizing sequence under `Q`. -/
theorem isLocalizingSequence_absoluteContinuousDensityExit
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    IsLocalizingSequence F (absoluteContinuousDensityExit Q P F) Q :=
  { isStoppingTime := isStoppingTime_absoluteContinuousDensityExit hF
    tendsto_top := ae_tendsto_absoluteContinuousDensityExit hQP hF
    mono := Eventually.of_forall monotone_absoluteContinuousDensityExit }

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- A cadlag density has a positive left-limit lower bound at every positive
time up to the corresponding exit. -/
theorem absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit
    {n : ℕ} {t : ℝ≥0} {ω : Ω}
    (hpath : IsCadlagPath (densityProcess Q P F · ω)) (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) ≤ absoluteContinuousDensityExit Q P F n ω) :
    (absoluteContinuousDensityThreshold n : ℝ) ≤
      leftLimitProcess (densityProcess Q P F) t ω := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  apply ge_of_tendsto (hpath.tendsto_leftLimitProcess ht0.ne')
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact absoluteContinuousDensityThreshold_le_of_lt_exit
    (WithTop.coe_lt_coe.mpr hs |>.trans_le ht)

omit [IsProbabilityMeasure Q] in
/-- Under the target law, one common full-measure event carries the left-limit
lower bound for every localizer and positive time. -/
theorem ae_absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit
    (hQP : Q ≪ P) :
    ∀ᵐ ω ∂Q, ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      (t : WithTop ℝ≥0) ≤ absoluteContinuousDensityExit Q P F n ω →
      (absoluteContinuousDensityThreshold n : ℝ) ≤
        leftLimitProcess (densityProcess Q P F) t ω := by
  filter_upwards [hQP.ae_le
      (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F))]
    with ω hω
  exact fun n t ht0 ht ↦
    absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit hω ht0 ht

omit [IsProbabilityMeasure Q] in
/-- Consequently the reciprocal density left limit is nonnegative and locally
bounded by the reciprocal geometric threshold. -/
theorem ae_inv_leftLimit_densityProcess_bounds_of_le_exit
    (hQP : Q ≪ P) :
    ∀ᵐ ω ∂Q, ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      (t : WithTop ℝ≥0) ≤ absoluteContinuousDensityExit Q P F n ω →
      0 ≤ 1 / leftLimitProcess (densityProcess Q P F) t ω ∧
        1 / leftLimitProcess (densityProcess Q P F) t ω ≤
          1 / (absoluteContinuousDensityThreshold n : ℝ) := by
  filter_upwards
      [ae_absoluteContinuousDensityThreshold_le_leftLimit_of_le_exit hQP]
    with ω hω
  intro n t ht0 ht
  have hlower := hω n t ht0 ht
  have hthresholdPos : (0 : ℝ) < (absoluteContinuousDensityThreshold n : ℝ) := by
    exact_mod_cast absoluteContinuousDensityThreshold_pos n
  have hpos : 0 < leftLimitProcess (densityProcess Q P F) t ω :=
    hthresholdPos.trans_le hlower
  exact ⟨by positivity,
    one_div_le_one_div_of_le hthresholdPos hlower⟩

end ProbabilityTheory
