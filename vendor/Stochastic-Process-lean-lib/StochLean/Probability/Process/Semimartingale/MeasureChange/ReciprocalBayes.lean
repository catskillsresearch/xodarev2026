/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.EquivalentDensity
public import StochLean.Probability.Process.Filtration.MeasureChange
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Reciprocal densities and Bayes' formula at a fixed time

For equivalent probability measures, the two canonical density processes are
reciprocals at every fixed time, almost surely.  Under one-way absolute
continuity, Bayes' formula first takes a multiplication form under the source
measure; strict positivity of the density under the target measure then gives
the usual division form.

All assertions in this file are coordinatewise in a fixed deterministic time.
They do not assert a simultaneous reciprocal identity at every time, a
stopped-time identity, or a Girsanov theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- At a fixed time, the density of `Q` with respect to `P` is the reciprocal
of the reverse density, `Q`-almost surely.  Mutual absolute continuity is used
both for the reciprocal Radon--Nikodym identity and to identify the reverse
trimmed density with its conditional-expectation process. -/
theorem densityProcess_reverse_ae_eq_inv (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) (t : ℝ≥0) :
    densityProcess Q P F t =ᵐ[Q] fun ω ↦ 1 / densityProcess P Q F t ω := by
  let hm : F t ≤ mΩ := F.le t
  have hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  have htrimQP : Q.trim hm ≪ P.trim hm := hQP.trim hm
  have hforward :
      (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal) =ᵐ[Q.trim hm]
        P[terminalDensity Q P | F t] :=
    htrimQP.ae_le (toReal_rnDeriv_trim hm hQP)
  have hreverse :
      (fun ω ↦ ((P.trim hm).rnDeriv (Q.trim hm) ω).toReal) =ᵐ[Q.trim hm]
        Q[terminalDensity P Q | F t] :=
    toReal_rnDeriv_trim hm hPQ
  have hrecip_trim :
      P[terminalDensity Q P | F t] =ᵐ[Q.trim hm]
        fun ω ↦ 1 / Q[terminalDensity P Q | F t] ω := by
    filter_upwards [Measure.inv_rnDeriv' htrimQP, hforward, hreverse]
      with ω hω_inv hω_forward hω_reverse
    rw [← hω_forward, ← hω_reverse, ← hω_inv]
    simp only [Pi.inv_apply, ENNReal.toReal_inv, one_div]
  have hrecip :
      P[terminalDensity Q P | F t] =ᵐ[Q]
        fun ω ↦ 1 / Q[terminalDensity P Q | F t] ω :=
    ae_eq_of_ae_eq_trim hrecip_trim
  filter_upwards [hQP.ae_le (densityProcess_ae_eq_condExp (Q := Q) hF t),
      densityProcess_ae_eq_condExp (P := Q) (Q := P) hFQ t, hrecip]
    with ω hω_forward hω_reverse hω_recip
  rw [hω_forward, hω_reverse]
  exact hω_recip

/-- Source-measure version of the fixed-time reciprocal density identity. -/
theorem densityProcess_reverse_ae_eq_inv_under_source (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) (t : ℝ≥0) :
    densityProcess Q P F t =ᵐ[P] fun ω ↦ 1 / densityProcess P Q F t ω :=
  hPQ.ae_le (densityProcess_reverse_ae_eq_inv hQP hPQ hF t)

/-- Multiplication form of Bayes' formula.  It requires only `Q ≪ P` and
integrability under `Q`; no reverse absolute continuity or quotient
integrability is needed. -/
theorem densityProcess_mul_condExp_ae_eq (hQP : Q ≪ P) (hF : F.IsUsual P)
    {Y : Ω → ℝ} (hY : Integrable Y Q) (t : ℝ≥0) :
    (fun ω ↦ densityProcess Q P F t ω * Q[Y | F t] ω) =ᵐ[P]
      P[fun ω ↦ terminalDensity Q P ω * Y ω | F t] := by
  let V : Ω → ℝ := Q[Y | F t]
  have hV : Integrable V Q := integrable_condExp
  have hDV : Integrable (fun ω ↦ terminalDensity Q P ω * V ω) P := by
    simpa only [terminalDensity] using
      (integrable_toReal_rnDeriv_mul_iff hQP).2 hV
  have hDY : Integrable (fun ω ↦ terminalDensity Q P ω * Y ω) P := by
    simpa only [terminalDensity] using
      (integrable_toReal_rnDeriv_mul_iff hQP).2 hY
  have hcond_pair :
      P[fun ω ↦ terminalDensity Q P ω * V ω | F t] =ᵐ[P]
        P[fun ω ↦ terminalDensity Q P ω * Y ω | F t] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (F.le t) hDY
    · intro s hs _
      exact integrable_condExp.integrableOn
    · intro s hs _
      calc
        (∫ ω in s, P[fun x ↦ terminalDensity Q P x * V x | F t] ω ∂P) =
            ∫ ω in s, terminalDensity Q P ω * V ω ∂P :=
          setIntegral_condExp (F.le t) hDV hs
        _ = ∫ ω in s, V ω ∂Q := by
          simpa only [terminalDensity] using
            (setIntegral_toReal_rnDeriv_mul hQP (F.le t s hs) (f := V))
        _ = ∫ ω in s, Y ω ∂Q :=
          setIntegral_condExp (F.le t) hY hs
        _ = ∫ ω in s, terminalDensity Q P ω * Y ω ∂P := by
          simpa only [terminalDensity] using
            (setIntegral_toReal_rnDeriv_mul hQP (F.le t s hs) (f := Y)).symm
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
  have hpull :
      P[fun ω ↦ terminalDensity Q P ω * V ω | F t] =ᵐ[P]
        fun ω ↦ P[terminalDensity Q P | F t] ω * V ω := by
    change P[terminalDensity Q P * V | F t] =ᵐ[P]
      P[terminalDensity Q P | F t] * V
    exact condExp_mul_of_stronglyMeasurable_right
      stronglyMeasurable_condExp hDV (integrable_terminalDensity Q P)
  filter_upwards [densityProcess_ae_eq_condExp (Q := Q) hF t,
      hpull.symm.trans hcond_pair]
    with ω hω_density hω_bayes
  rw [hω_density]
  exact hω_bayes

/-- Division form of Bayes' formula under the target measure.  The quotient
is justified by fixed-time `Q`-almost-sure strict positivity of the density. -/
theorem condExp_ae_eq_div_densityProcess (hQP : Q ≪ P) (hF : F.IsUsual P)
    {Y : Ω → ℝ} (hY : Integrable Y Q) (t : ℝ≥0) :
    Q[Y | F t] =ᵐ[Q] fun ω ↦
      P[fun x ↦ terminalDensity Q P x * Y x | F t] ω /
        densityProcess Q P F t ω := by
  filter_upwards [hQP.ae_le (densityProcess_mul_condExp_ae_eq hQP hF hY t),
      densityProcess_pos_ae hQP hF t]
    with ω hω_mul hω_pos
  apply (eq_div_iff hω_pos.ne').2
  simpa only [mul_comm] using hω_mul

/-- Under equivalence, the division form of Bayes' formula also holds under
the source measure. -/
theorem condExp_ae_eq_div_densityProcess_under_source (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) {Y : Ω → ℝ} (hY : Integrable Y Q) (t : ℝ≥0) :
    Q[Y | F t] =ᵐ[P] fun ω ↦
      P[fun x ↦ terminalDensity Q P x * Y x | F t] ω /
        densityProcess Q P F t ω :=
  hPQ.ae_le (condExp_ae_eq_div_densityProcess hQP hF hY t)

end ProbabilityTheory
