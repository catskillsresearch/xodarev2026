/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableTerminalEnergy
public import StochLean.Probability.Martingale.Convergence.MonotoneL1

/-! # Uniform energy of bounded-supermartingale Doob approximants

The increasing part is the existing `predictablePart (-X)`. If `|X| ≤ K`, its
conditional remaining means are bounded by `2 K` and every terminal second
moment by `8 K²`, independently of the number of sampling points. The actual
increasing terminal limit is constructed and satisfies the same bound.
-/

@[expose] public section

open ProbabilityTheory Filter Finset
open scoped ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem condExp_doob_increasing_tail (hX : Supermartingale X F P) {k n : ℕ} (hkn : k ≤ n) :
    P[predictablePart (-X) F P n - predictablePart (-X) F P k | F k] =ᵐ[P]
      X k - P[X n | F k] := by
  let A := predictablePart (-X) F P
  let M := -martingalePart (-X) F P
  obtain ⟨hM, hA, _, _, he, _, _, hiA, _⟩ := hX.doob_decomposition_data
  have hAN : A n = M n - X n := by
    funext ω
    have h := congrFun (congrFun he n) ω
    change M n ω - A n ω = X n ω at h
    change A n ω = M n ω - X n ω
    linarith
  have hceA : P[A k | F k] = A k :=
    condExp_of_stronglyMeasurable (F.le k) (hA.stronglyAdapted k) (hiA k)
  have hceN : P[A n | F k] =ᵐ[P] M k - P[X n | F k] := by
    rw [hAN]
    exact (condExp_sub (hM.integrable n) (hX.integrable n) (F k)).trans
      ((hM.condExp_ae_eq hkn).sub EventuallyEq.rfl)
  have hce := (condExp_sub (hiA n) (hiA k) (F k)).trans
    (hceN.sub (Eventually.of_forall fun ω ↦ congrFun hceA ω))
  filter_upwards [hce] with ω hω
  have h := congrFun (congrFun he k) ω
  change M k ω - A k ω = X k ω at h
  change P[A n - A k | F k] ω = (M k ω - P[X n | F k] ω) - A k ω at hω
  change P[A n - A k | F k] ω = X k ω - P[X n | F k] ω
  linarith

theorem integral_sq_doob_increasing_le_of_bound (hX : Supermartingale X F P)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ K) (n : ℕ) :
    (∫ ω, predictablePart (-X) F P n ω ^ 2 ∂P) ≤ 8 * K ^ 2 := by
  let A := predictablePart (-X) F P
  obtain ⟨_, hp, h0, _, _, hm, _, _, _⟩ := hX.doob_decomposition_data
  have hL (k : ℕ) : MemLp (X k) 2 P := by
    apply MemLp.of_bound (hX.integrable k).aestronglyMeasurable K
    simpa only [Real.norm_eq_abs] using hb k
  have hLA (k : ℕ) : MemLp (A k) 2 P := by
    change MemLp (∑ i ∈ range k, P[(-X) (i + 1) - (-X) i | F i]) 2 P
    apply memLp_finsetSum'
    intro i _
    exact ((hL (i + 1)).neg.sub (hL i).neg).condExp (by norm_num)
  have htail (k : ℕ) (hkn : k ≤ n) : P[A n - A k | F k] ≤ᵐ[P] (fun _ ↦ 2 * K) := by
    have hlo : (fun _ : Ω ↦ -K) ≤ᵐ[P] X n := (hb n).mono fun _ hω ↦ (abs_le.mp hω).1
    have hcl := condExp_mono (m := F k) (integrable_const (-K)) (hX.integrable n) hlo
    rw [condExp_const (F.le k)] at hcl
    filter_upwards [hX.condExp_doob_increasing_tail hkn, hcl, hb k] with ω he hle hω
    change P[A n - A k | F k] ω = X k ω - P[X n | F k] ω at he
    change -K ≤ P[X n | F k] ω at hle
    have hu := (abs_le.mp hω).2
    linarith
  have h := hp.integral_sq_le_of_condExp_tail_bound hm
    (Eventually.of_forall fun ω ↦ congrFun h0 ω) hLA (by positivity : 0 ≤ 2 * K) n htail
  convert h using 1
  ring

theorem exists_memLp_two_doob_increasing_limit_of_bound (hX : Supermartingale X F P)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ K) :
    let A := predictablePart (-X) F P
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ 8 * K ^ 2 ∧
      (∀ᵐ ω ∂P, (∀ n, A n ω ≤ Z ω) ∧ Tendsto (fun n ↦ A n ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable A 1 P ∧ Tendsto (fun n ↦ eLpNorm (A n - Z) 1 P) atTop (𝓝 0) := by
  intro A
  obtain ⟨_, hp, _, _, _, hm, hn, hi, hmean⟩ := hX.doob_decomposition_data
  have hE (n : ℕ) : (∫ ω, A n ω ∂P) ≤ 2 * K := by
    rw [hmean n]
    have hu := integral_mono_ae (hX.integrable 0) (integrable_const K)
      ((hb 0).mono fun _ hω ↦ (abs_le.mp hω).2)
    have hl := integral_mono_ae (integrable_const (-K)) (hX.integrable n)
      ((hb n).mono fun _ hω ↦ (abs_le.mp hω).1)
    simp only [integral_const, probReal_univ, one_smul] at hu hl
    linarith
  obtain ⟨Z, hiZ, hlZ, huZ, hLZ⟩ :=
    hm.exists_integrable_limit_of_nonneg_of_integral_bounded hp.stronglyAdapted.adapted hi
      (fun n ↦ hn.mono fun _ hω ↦ hω n) hE
  have hL (k : ℕ) : MemLp (A k) 2 P := by
    change MemLp (∑ i ∈ range k, P[(-X) (i + 1) - (-X) i | F i]) 2 P
    apply memLp_finsetSum'
    intro i _
    have hXi (j : ℕ) : MemLp (X j) 2 P := MemLp.of_bound
      (hX.integrable j).aestronglyMeasurable K (by simpa only [Real.norm_eq_abs] using hb j)
    exact ((hXi (i + 1)).neg.sub (hXi i).neg).condExp (by norm_num)
  obtain ⟨hiSq, hSq⟩ := integrable_and_integral_le_of_nonneg_ae_tendsto
    (fun n ↦ (hL n).integrable_sq) (fun n ↦ Eventually.of_forall fun ω ↦ sq_nonneg (A n ω))
    (hlZ.mono fun _ hω ↦ hω.2.pow 2) (by positivity : 0 ≤ 8 * K ^ 2)
    (hX.integral_sq_doob_increasing_le_of_bound hK hb)
  exact ⟨Z, (memLp_two_iff_integrable_sq hiZ.aestronglyMeasurable).mpr hiSq, hSq, hlZ, huZ, hLZ⟩

end MeasureTheory.Supermartingale
