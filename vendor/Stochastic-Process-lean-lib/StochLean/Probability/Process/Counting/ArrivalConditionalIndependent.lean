/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Probability.Kernel.CondDistribIndependent
public import StochLean.ForMathlib.Probability.Kernel.CondDistribOnHistoryEvent
public import StochLean.Probability.Process.Counting.ArrivalPrefixDurations
public import Mathlib.Algebra.BigOperators.Fin

/-! # Independent latent durations on the actual finite-history event

The original arrival history consists of literal prefix sums of the latent
durations. Independence of disjoint finite coordinate vectors, followed by
the measurable prefix-sum map, makes the next latent duration independent
of that history. Its original conditional law is therefore its marginal law.

On the history event where the preceding prefix is finite, the actual
absorbing gap equals the next latent duration. Native conditional-kernel
equality on a history event transfers the marginal identity to that actual
gap. After an infinite prefix the identity is deliberately not asserted.
Neither positivity nor nonexplosion is needed, and the history is not
assumed to be initially available in any filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-- Independent latent durations give the original next-gap marginal law
conditional on the actual arrival history, on the finite preceding-prefix
event. No global independence of the absorbing gaps is asserted. -/
theorem condDistrib_arrivalInterarrival_eq_marginal_of_iIndepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ → Ω → WithTop ℝ≥0} (hd : ∀ n, Measurable (d n))
    (hind : iIndepFun d P) (n : ℕ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let Γ : ℕ → Ω → WithTop ℝ≥0 := fun k ω ↦ ∑ j ∈ Finset.range (k + 1), d j ω
    let H : Ω → Fin n → WithTop ℝ≥0 := fun ω i ↦ Γ i ω
    ∀ᵐ ω ∂P, (∑ j ∈ Finset.range n, d j ω) ≠ ⊤ →
      condDistrib (fun v ↦ arrivalInterarrival (fun k ↦ Γ k v) n) H P (H ω) =
        P.map (d n) := by
  classical
  intro hSB Γ H
  let : StandardBorelSpace (WithTop ℝ≥0) := hSB
  let : MeasurableAdd₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableAdd₂ ℝ≥0∞)
  have hΓ : ∀ k, Measurable (Γ k) := fun k ↦
    (Finset.range (k + 1)).measurable_fun_sum fun j _ ↦ hd j
  have hH : Measurable H := measurable_pi_lambda _ fun i ↦ hΓ i
  let S : Ω → WithTop ℝ≥0 := fun ω ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  have hS : Measurable S := measurable_arrivalInterarrival hΓ n
  have hIndep : IndepFun (d n) H P := by
    let R : (Finset.range n → WithTop ℝ≥0) → Fin n → WithTop ℝ≥0 := fun z i ↦
      ∑ j : Fin (i.val + 1),
        z ⟨j, Finset.mem_range.mpr (j.isLt.trans_le (Nat.succ_le_of_lt i.isLt))⟩
    have hRmeas : Measurable R := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact Finset.univ.measurable_fun_sum fun (j : Fin (i.val + 1)) _ ↦
        measurable_pi_apply
          (⟨j, Finset.mem_range.mpr
            (j.isLt.trans_le (Nat.succ_le_of_lt i.isLt))⟩ : Finset.range n)
    have hR : (fun ω ↦ R (fun j : Finset.range n ↦ d j ω)) = H := by
      funext ω i
      change (∑ j : Fin (i.val + 1), d j ω) = ∑ j ∈ Finset.range (i.val + 1), d j ω
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ d j ω) (i.val + 1)
    have hi := iIndepFun.indepFun_finset ({n} : Finset ℕ) (Finset.range n)
      (Finset.disjoint_singleton_left.mpr Finset.notMem_range_self) hind hd
    have hi' := hi.comp
      (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ))) hRmeas
    change IndepFun (d n) (fun ω ↦ R (fun j : Finset.range n ↦ d j ω)) P at hi'
    rwa [hR] at hi'
  obtain ⟨B, hB, hBiff⟩ : ∃ B : Set (Fin n → WithTop ℝ≥0), MeasurableSet B ∧
      ∀ ω, H ω ∈ B ↔ (∑ j ∈ Finset.range n, d j ω) ≠ ⊤ := by
    cases n with
    | zero =>
        refine ⟨univ, MeasurableSet.univ, ?_⟩
        intro ω
        change True ↔ ((0 : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤
        exact ⟨fun _ ↦ WithTop.coe_ne_top, fun _ ↦ trivial⟩
    | succ k =>
        refine ⟨{z | z (Fin.last k) ≠ ⊤}, ?_, ?_⟩
        · exact (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl.preimage
            (measurable_pi_apply (Fin.last k))
        · intro ω
          rfl
  have hsame : ∀ᵐ ω ∂P, H ω ∈ B → S ω = d n ω := ae_of_all P fun ω hω ↦
    arrivalInterarrival_sum_range_eq_of_prefix_ne_top (fun k ↦ d k ω) n ((hBiff ω).mp hω)
  have hlocal := condDistrib_comp_ae_eq_on_history_event hS (hd n) hH hB hsame
  have hmarginal := ae_of_ae_map hH.aemeasurable
    (condDistrib_ae_eq_const_of_indepFun (hd n) hH hIndep)
  filter_upwards [hlocal, hmarginal] with ω hω hm hfin
  exact (hω ((hBiff ω).mpr hfin)).trans (by simpa only [Kernel.const_apply] using hm)

end ProbabilityTheory
