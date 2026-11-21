/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoredCrudeCompensator
public import StochLean.Probability.Process.Semimartingale.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.UsualCongruence

/-! # Actual net rates and the net-equals-crude censoring corollary

The net rate is the native right limit of the original lifetime's window
probability divided by its own survival and the window width. It is not an
arbitrary supplied density. Absolute continuity of the actual real lifetime
law identifies this rate almost everywhere with its native RN density divided
by survival, by specializing the crude-rate theorem to censoring at infinity.
The latter lifetime is only used in comparisons, never evaluated by `untopA`.

The final theorem retains the explicit mathematical assumption that net and
crude rates agree almost everywhere at nonnegative times with positive joint
survival. No equality is required after joint survival has vanished. Almost
every observation lifetime has positive closed survival, hence every time in
its actual stopped integration range has positive joint survival. One path
event therefore equates all stopped primitives. Relative completeness of the
genuine usual filtration transfers the actual local-martingale property to
the net-rate remainder. No adaptedness, integrability, primitive limit, or
compensator certificate is an extra input.

Native filter limits outside the proved almost-everywhere convergence event
and quotients at zero survival are totalizations; at zero survival they are
not interpreted as conditional probabilities.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {T U : Ω → WithTop ℝ≥0}

/-- The original lifetime's actual net right-window rate, totalized by the
native filter limit. Existence of that limit is a separate conclusion. -/
noncomputable def lifetimeNetRate (P : Measure Ω) (T : Ω → WithTop ℝ≥0)
    (t : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun h : ℝ ↦
    (P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
      T ω < ((t + h).toNNReal : WithTop ℝ≥0)} /
      P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω}) / h)

private theorem lifetimeNetRate_eq_censoredCrudeRate_top
    (P : Measure Ω) (T : Ω → WithTop ℝ≥0) (t : ℝ) :
    lifetimeNetRate P T t = censoredCrudeRate P T (fun _ ↦ ⊤) t := by
  simp only [lifetimeNetRate, censoredCrudeRate, le_top, and_true]

/-- The genuine net rate is the original real lifetime law's native RN
density divided by its own survival at almost every nonnegative time. -/
theorem ae_lifetimeNetRate_eq_rnDeriv_div_survival [IsFiniteMeasure P]
    (hT : Measurable T)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
      lifetimeNetRate P T t =
        ((P.map (fun ω ↦ ((T ω).untopA : ℝ))).rnDeriv volume t).toReal /
          P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ T ω} := by
  have he := ae_censoredCrudeRate_eq_rnDeriv_div_survival
    (U := fun _ ↦ ⊤) hT measurable_const hAC
  filter_upwards [he] with t ht hnonneg
  simpa only [← lifetimeNetRate_eq_censoredCrudeRate_top, le_top, ofPred_true,
    Measure.restrict_univ, and_true] using ht hnonneg

open Classical in
/-- If the actual net and crude rates agree almost everywhere where joint
survival is positive, subtracting the stopped net-rate primitive from the
censored arrival count gives a local martingale in the genuine usual
observed-pair filtration. -/
theorem isLocalMartingale_censoredCount_sub_netRate_integral
    [IsProbabilityMeasure P] (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume)
    (hnet : ∀ᵐ x : ℝ ∂volume, 0 ≤ x →
      0 < P.real {ω | (x.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        (x.toNNReal : WithTop ℝ≥0) ≤ U ω} →
      lifetimeNetRate P T x = censoredCrudeRate P T U x) :
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    IsLocalMartingale
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        (if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω then (1 : ℝ) else 0) -
          ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
            lifetimeNetRate P T x)
      (F.usualAugmentation P) P.completion := by
  let F := Filtration.natural _
    (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
  let G := F.usualAugmentation P
  let μ := P.map (fun ω ↦ min (T ω) (U ω))
  let M := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    (if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω then (1 : ℝ) else 0) -
      ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
        censoredCrudeRate P T U x
  let N := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    (if min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω then (1 : ℝ) else 0) -
      ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA : ℝ),
        lifetimeNetRate P T x
  have hM : IsLocalMartingale M G P.completion :=
    isLocalMartingale_censoredCount_sub_crudeRate_integral hT hU hAC
  have hG : G.IsUsual P.completion := F.usualAugmentation_isUsual P
  have hpositive : ∀ᵐ ω ∂P.completion, 0 < μ (Ici (min (T ω) (U ω))) :=
    ae_of_ae_map (μ := P) (hT.min hU).aemeasurable (ae_pos_measure_Ici μ)
  have he : Indistinguishable M N P.completion := by
    filter_upwards [hpositive] with ω hω t
    let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (min (T ω) (U ω))).untopA
    have hfinite : min (t : WithTop ℝ≥0) (min (T ω) (U ω)) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (min (T ω) (U ω)) := by
      dsimp only [u]
      rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
    change _ - (∫ x in (0 : ℝ)..(u : ℝ), censoredCrudeRate P T U x) =
      _ - ∫ x in (0 : ℝ)..(u : ℝ), lifetimeNetRate P T x
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hnet] with x hx hmem
    rw [uIoc_of_le (NNReal.coe_nonneg u)] at hmem
    have hxu : x.toNNReal ≤ u := Real.toNNReal_le_iff_le_coe.mpr hmem.2
    have hxlife : (x.toNNReal : WithTop ℝ≥0) ≤ min (T ω) (U ω) :=
      (WithTop.coe_le_coe.mpr hxu).trans (hu.le.trans (min_le_right _ _))
    have hsurv : 0 < μ (Ici (x.toNNReal : WithTop ℝ≥0)) :=
      hω.trans_le (measure_mono (Ici_subset_Ici.mpr hxlife))
    have hmass : 0 < P {ω | (x.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        (x.toNNReal : WithTop ℝ≥0) ≤ U ω} := by
      rw [← censored_survival_measure_eq (P := P) hT hU x.toNNReal]
      exact hsurv
    have hreal : 0 < P.real {ω | (x.toNNReal : WithTop ℝ≥0) ≤ T ω ∧
        (x.toNNReal : WithTop ℝ≥0) ≤ U ω} :=
      ENNReal.toReal_pos hmass.ne' (measure_ne_top P _)
    exact (hx hmem.1.le hreal).symm
  exact hM.congr hG ((hM.isSemimartingale hG).congr_of_usual hG he).adapted he

end ProbabilityTheory
