/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.DeviationEvents
public import StochLean.ForMathlib.Topology.UniformCauchy

/-! # UCP-Cauchy sequences and a common-event uniform Cauchy subsequence

The criterion uses the existing UCP strict-deviation events. The subsequence is
constructed by a summable-probability diagonal, without assuming measurable paths
or continuity of an outer measure on arbitrary decreasing sets.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

def CauchyUCP (P : Measure Ω) (X : ℕ → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ,
    ∀ m n, N ≤ m → N ≤ n → P {ω | ∃ t ≤ T, ε < ‖X m t ω - X n t ω‖} ≤ η

theorem measure_ucp_deviation_triangle (X Y Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ε : ℝ) :
    P {ω | ∃ t ≤ T, ε < ‖X t ω - Z t ω‖} ≤
      P {ω | ∃ t ≤ T, ε / 2 < ‖X t ω - Y t ω‖} +
        P {ω | ∃ t ≤ T, ε / 2 < ‖Y t ω - Z t ω‖} := by
  apply (measure_mono (t := {ω | ∃ t ≤ T, ε / 2 < ‖X t ω - Y t ω‖} ∪
    {ω | ∃ t ≤ T, ε / 2 < ‖Y t ω - Z t ω‖}) ?_).trans (measure_union_le _ _)
  rintro ω ⟨t, ht, hω⟩
  by_cases hXY : ε / 2 < ‖X t ω - Y t ω‖
  · exact Or.inl ⟨t, ht, hXY⟩
  · refine Or.inr ⟨t, ht, ?_⟩
    have h := dist_triangle (X t ω) (Y t ω) (Z t ω)
    simp only [dist_eq_norm_sub] at h
    have hXY := le_of_not_gt hXY
    linarith

theorem TendstoUCP.cauchyUCP (h : TendstoUCP P X atTop Y) : CauchyUCP P X := by
  intro T ε hε η hη
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendstoUCP_iff_measure_exists_norm_lt.mp h T (ε / 2) (half_pos hε))
    (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  have htri := measure_ucp_deviation_triangle (P := P) (X m) Y (X n) T ε
  simp only [norm_sub_rev (Y _ _) (X n _ _)] at htri
  exact htri.trans ((add_le_add (hN m hm) (hN n hn)).trans (ENNReal.add_halves η).le)

theorem CauchyUCP.tendstoUCP_of_subseq (hc : CauchyUCP P X) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hs : TendstoUCP P (X ∘ k) atTop Y) :
    TendstoUCP P X atTop Y := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨N, hN⟩ := hc T (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨K, hK⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendstoUCP_iff_measure_exists_norm_lt.mp hs T (ε / 2) (half_pos hε))
    (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨j, hjN, hjK⟩ := ((hk.eventually (eventually_ge_atTop N)).and
    (eventually_ge_atTop K)).exists
  refine ⟨N, fun n hn ↦ ?_⟩
  exact (measure_ucp_deviation_triangle (X n) (X (k j)) Y T ε).trans
    ((add_le_add (hN n (k j) hn hjN) (hK j hjK)).trans (ENNReal.add_halves η).le)

theorem CauchyUCP.exists_seq_ae_locallyUniform_cauchy (hc : CauchyUCP P X) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      UniformCauchySeqOn (fun n t ↦ X (k n) t ω) atTop (Icc 0 T) := by
  classical
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hrpos : ∀ n, 0 < r n := fun n ↦ ENNReal.pow_pos (by simp) n
  have hrfin : (∑' n, r n) ≠ ∞ := by
    simpa only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ i m n, N i ≤ m → N i ≤ n →
      P {ω | ∃ t ≤ (i : ℝ≥0), (2⁻¹ : ℝ) ^ i < ‖X m t ω - X n t ω‖} ≤ r i := by
    choose N hN using fun i : ℕ ↦ hc i ((2⁻¹ : ℝ) ^ i) (by positivity) (r i) (hrpos i)
    exact ⟨N, hN⟩
  let k : ℕ → ℕ := fun n ↦ n + ∑ i ∈ Finset.range (n + 1), N i
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    exact (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (N i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))).trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp only [k]
    rw [Finset.sum_range_succ (n := n + 1)]
    omega
  let A : ℕ → Set Ω := fun n ↦
    {ω | ∃ t ≤ (n : ℝ≥0), (2⁻¹ : ℝ) ^ n < ‖X (k n) t ω - X (k (n + 1)) t ω‖}
  have hA : ∀ n, P (A n) ≤ r n := fun n ↦
    hN n (k n) (k (n + 1)) (hkN n) ((hkN n).trans (hk.monotone (Nat.le_succ n)))
  have hsumA : (∑' n, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hrfin (ENNReal.tsum_le_tsum hA)
  refine ⟨k, hk, ?_⟩
  filter_upwards [ae_eventually_notMem hsumA] with ω hω
  intro T
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  apply uniformCauchySeqOn_of_eventually_geometric
  filter_upwards [hω, eventually_ge_atTop NT] with n hn hNTn
  intro t ht
  have htn : t ≤ (n : ℝ≥0) := ht.2.trans (hNT.trans (by exact_mod_cast hNTn))
  have hbound : ‖X (k n) t ω - X (k (n + 1)) t ω‖ ≤ (2⁻¹ : ℝ) ^ n :=
    le_of_not_gt (fun h ↦ hn ⟨t, htn, h⟩)
  rw [edist_dist, dist_eq_norm_sub]
  convert ENNReal.ofReal_le_ofReal hbound using 1
  simp [ENNReal.ofReal_pow, ENNReal.inv_pow]

end ProbabilityTheory
