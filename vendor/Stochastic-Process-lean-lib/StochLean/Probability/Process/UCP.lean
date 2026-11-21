/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Supremum
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def compactDeviation (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖X t ω - Y t ω‖

theorem enorm_sub_le_compactDeviation {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    ENNReal.ofReal ‖X t ω - Y t ω‖ ≤ compactDeviation X Y T ω :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)

theorem compactDeviation_mono {S T : ℝ≥0} (hST : S ≤ T) (ω : Ω) :
    compactDeviation X Y S ω ≤ compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact enorm_sub_le_compactDeviation (ht.trans hST) ω

@[simp] theorem compactDeviation_self (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    compactDeviation X X T ω = 0 := by simp [compactDeviation]

theorem compactDeviation_comm (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    compactDeviation X Y T ω = compactDeviation Y X T ω := by
  simp only [compactDeviation, norm_sub_rev]

theorem compactDeviation_eq_dense {T : ℝ≥0} {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) (hY : IsRightContinuousPath (Y · ω)) :
    compactDeviation X Y T ω =
      denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T ω := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact ofReal_le_denseRunningSupremum_of_rightContinuous ht
      (fun s ↦ ((hX s).sub (hY s)).norm)
  · apply iSup_le
    intro n
    exact enorm_sub_le_compactDeviation (min_le_left _ _) ω

theorem measurable_compactDeviation (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t))
    (hrX : ∀ ω, IsRightContinuousPath (X · ω))
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (T : ℝ≥0) :
    Measurable (compactDeviation X Y T) := by
  have heq : compactDeviation X Y T =
      denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T :=
    funext fun ω ↦ compactDeviation_eq_dense (hrX ω) (hrY ω)
  rw [heq]
  exact measurable_denseRunningSupremum (fun t ↦ ((hX t).sub (hY t)).norm) T

theorem aemeasurable_compactDeviation (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t))
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P) (T : ℝ≥0) :
    AEMeasurable (compactDeviation X Y T) P := by
  have hm := (measurable_denseRunningSupremum
    (fun t ↦ ((hX t).sub (hY t)).norm) T).aemeasurable (μ := P)
  apply hm.congr
  filter_upwards [hrX, hrY] with ω hx hy
  exact (compactDeviation_eq_dense hx hy).symm

/-- Compact-by-compact convergence in probability of the uniform deviations. -/
def TendstoUCP {ι : Type*} (P : Measure Ω) (X : ι → ℝ≥0 → Ω → ℝ)
    (l : Filter ι) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ T : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε →
    Tendsto (fun i ↦ P {ω | ε ≤ compactDeviation (X i) Y T ω}) l (𝓝 0)

theorem TendstoUCP.fixedTime {ι : Type*} {X : ι → ℝ≥0 → Ω → ℝ}
    {l : Filter ι} (hX : TendstoUCP P X l Y) (t : ℝ≥0) :
    TendstoInMeasure P (fun i ↦ X i t) l (Y t) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hX t ε hε)
    (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  intro ω hω
  change ε ≤ edist (X i t ω) (Y t ω) at hω
  rw [edist_dist, dist_eq_norm_sub] at hω
  exact hω.trans (enorm_sub_le_compactDeviation (X := X i) (Y := Y) (t := t) le_rfl ω)

theorem TendstoUCP.comp {ι κ : Type*} {X : ι → ℝ≥0 → Ω → ℝ}
    {l : Filter ι} {v : Filter κ} {s : κ → ι}
    (hX : TendstoUCP P X l Y) (hs : Tendsto s v l) :
    TendstoUCP P (X ∘ s) v Y := fun T ε hε ↦ (hX T ε hε).comp hs

theorem tendstoUCP_const {ι : Type*} (l : Filter ι) (Y : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun _ : ι ↦ Y) l Y := by
  intro T ε hε
  simpa [not_le_of_gt hε] using
    (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))

/-- One subsequence converges uniformly on every compact interval on a single full-measure event.
The diagonal uses growing horizons and a summable sequence of exceptional probabilities. -/
theorem TendstoUCP.exists_seq_ae_locallyUniform {X : ℕ → ℝ≥0 → Ω → ℝ}
    (hX : TendstoUCP P X atTop Y) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        Tendsto (fun n ↦ compactDeviation (X (k n)) Y T ω) atTop (𝓝 0) := by
  classical
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hrpos : ∀ n, 0 < r n := fun n ↦ ENNReal.pow_pos (by simp) n
  have hrfin : (∑' n, r n) ≠ ∞ := by
    simpa only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)
  have hthreshold : ∀ n : ℕ, ∃ N : ℕ, ∀ j ≥ N,
      P {ω | r n ≤ compactDeviation (X j) Y n ω} ≤ r n := by
    intro n
    exact ENNReal.tendsto_atTop_zero.mp (hX n (r n) (hrpos n)) (r n) (hrpos n)
  choose N hN using hthreshold
  let k : ℕ → ℕ := fun n ↦ n + ∑ i ∈ Finset.range (n + 1), N i
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    have hsum : N n ≤ ∑ i ∈ Finset.range (n + 1), N i :=
      Finset.single_le_sum (fun i _ ↦ Nat.zero_le (N i)) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact hsum.trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp only [k]
    rw [Finset.sum_range_succ (n := n + 1)]
    omega
  let A : ℕ → Set Ω := fun n ↦ {ω | r n ≤ compactDeviation (X (k n)) Y n ω}
  have hA : ∀ n, P (A n) ≤ r n := fun n ↦ hN n (k n) (hkN n)
  have hsumA : (∑' n, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hrfin (ENNReal.tsum_le_tsum hA)
  refine ⟨k, hk, ?_⟩
  filter_upwards [ae_eventually_notMem hsumA] with ω hω
  intro T
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp hω
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨NE, hNE⟩ := ENNReal.tendsto_atTop_zero.mp
    (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hrfin) ε hε
  refine ⟨max NT (max NA NE), fun n hn ↦ ?_⟩
  have hTn : T ≤ (n : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NA NE)).trans hn)
  have hAn : compactDeviation (X (k n)) Y n ω < r n :=
    lt_of_not_ge (hNA n ((le_max_left NA NE).trans ((le_max_right NT (max NA NE)).trans hn)))
  exact (compactDeviation_mono hTn ω).trans (hAn.le.trans
    (hNE n ((le_max_right NA NE).trans ((le_max_right NT (max NA NE)).trans hn))))

end ProbabilityTheory
