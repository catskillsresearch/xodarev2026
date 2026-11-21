/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Reflection
public import StochLean.Probability.Brownian.UsualAugmentation
public import StochLean.Probability.Process.Semimartingale.KlenkeStoppingMoments
public import StochLean.Probability.Process.Stopping.RightContinuousHitting

/-! # Klenke Exercise 21.10.3

The first passage of a real Brownian motion through level one gives the requested
counterexample.  The stopped terminal value is one, hence has a finite second
moment, while the normalized bracket at the stopping time is not integrable.

There are two substantive points which are not hidden in assumptions here.

* Brownian reflection and Gaussian scaling show that the one-sided first-passage
  time is finite almost surely.
* If the terminal bracket were integrable, Klenke 21.75 applied to the finite
  truncations would make their terminal values uniformly integrable.  Their
  expectations are all zero, but they converge almost surely to one, a
  contradiction.

The final namespace instantiates this argument on the project-owned Brownian
probability space and its natural usual augmentation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

private theorem two_mul_standardGaussian_Ioi_zero :
    2 * gaussianReal 0 1 (Ioi 0) = 1 := by
  let μ : Measure ℝ := gaussianReal 0 1
  have hsymm : μ (Iio 0) = μ (Ioi 0) := by
    calc
      μ (Iio 0) = μ.map (fun x : ℝ ↦ -x) (Iio 0) := by
        rw [gaussianReal_map_neg, neg_zero]
      _ = μ ((fun x : ℝ ↦ -x) ⁻¹' Iio 0) :=
        Measure.map_apply measurable_neg measurableSet_Iio
      _ = μ (Ioi 0) := by
        congr 1
        ext x
        simp only [mem_preimage, mem_Iio, mem_Ioi, neg_lt_zero]
  letI : NullSingletonClass μ :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hzero : μ ({0} : Set ℝ) = 0 := measure_singleton 0
  have hdisj₁ : Disjoint (Iio (0 : ℝ)) ({0} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx hxeq
    exact (ne_of_lt hx) hxeq
  have hdisj₂ : Disjoint (Iio (0 : ℝ) ∪ {0}) (Ioi 0) := by
    rw [Set.disjoint_left]
    intro x hx hpos
    rcases hx with hx | hx
    · have hneg : x < 0 := hx
      have hpos' : 0 < x := hpos
      exact (not_lt_of_ge hpos'.le) hneg
    · have hzero' : x = 0 := hx
      have hpos' : 0 < x := hpos
      exact (ne_of_lt hpos') hzero'.symm
  have huniv : (Iio (0 : ℝ) ∪ {0}) ∪ Ioi 0 = Set.univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  calc
    2 * gaussianReal 0 1 (Ioi 0) = μ (Iio 0) + μ (Ioi 0) := by
      rw [hsymm, two_mul]
    _ = (μ (Iio 0) + μ {0}) + μ (Ioi 0) := by rw [hzero, add_zero]
    _ = μ (Iio 0 ∪ {0}) + μ (Ioi 0) := by
      congr 1
      exact (measure_union hdisj₁ (measurableSet_singleton 0)).symm
    _ = μ ((Iio 0 ∪ {0}) ∪ Ioi 0) := by
      exact (measure_union hdisj₂ measurableSet_Ioi).symm
    _ = μ Set.univ := by rw [huniv]
    _ = 1 := measure_univ

/-- A real Brownian motion with measurable coordinates and everywhere-continuous
paths crosses level one in finite time almost surely.  This is the recurrence
input needed by Klenke's example; it is proved from the reflection principle,
not assumed as a separate Brownian axiom. -/
theorem IsBrownianReal.ae_hittingAfter_Ioi_one_ne_top [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) :
    ∀ᵐ ω ∂P, hittingAfter B (Ioi 1) 0 ω ≠ ⊤ := by
  let μ : Measure ℝ := gaussianReal 0 1
  let c : ℕ → ℝ := fun n ↦ n + 1
  let T : ℕ → ℝ≥0 := fun n ↦ ⟨c n ^ 2, sq_nonneg (c n)⟩
  let D : ℕ → Set ℝ := fun n ↦ Ioi (1 / c n)
  let C : ℕ → Set Ω := fun n ↦
    {ω | ∃ t : ℝ≥0, t ≤ T n ∧ 1 < B t ω}
  have hcpos (n : ℕ) : 0 < c n := by
    dsimp only [c]
    positivity
  have hDmono : Monotone D := by
    intro n m hnm x hx
    change 1 / c m < x
    apply (one_div_le_one_div_of_le (hcpos n) ?_).trans_lt hx
    dsimp only [c]
    exact_mod_cast Nat.succ_le_succ hnm
  have hiD : (⋃ n, D n) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, D, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (by positivity : 0 < 1 / c n).trans hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, by simpa only [c] using hn⟩
  have htD : Tendsto (fun n ↦ μ (D n)) atTop (𝓝 (μ (Ioi 0))) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hDmono
    rwa [hiD] at h
  have ht2D : Tendsto (fun n ↦ 2 * μ (D n)) atTop (𝓝 1) := by
    have h := ENNReal.Tendsto.const_mul htD
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    have hhalf : 2 * μ (Ioi 0) = 1 := by
      simpa only [μ] using two_mul_standardGaussian_Ioi_zero
    simpa only [hhalf] using h
  have hscale (n : ℕ) :
      μ.map (fun x : ℝ ↦ c n * x) = gaussianReal 0 (T n) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      change c n ^ 2 * 1 = c n ^ 2
      ring
  have htail (n : ℕ) :
      P {ω | 1 < B (T n) ω} = μ (D n) := by
    calc
      P {ω | 1 < B (T n) ω} = gaussianReal 0 (T n) (Ioi 1) :=
        hB.toIsPreBrownianReal.hasLaw_eval (T n) |>.measure_eq measurableSet_Ioi
      _ = μ.map (fun x : ℝ ↦ c n * x) (Ioi 1) := by rw [hscale]
      _ = μ ((fun x : ℝ ↦ c n * x) ⁻¹' Ioi 1) :=
        Measure.map_apply (by fun_prop) measurableSet_Ioi
      _ = μ (D n) := by
        congr 1
        ext x
        simp only [mem_preimage, mem_Ioi, D]
        simpa only [mul_comm] using (div_lt_iff₀ (hcpos n)).symm
  have hCmeasure (n : ℕ) : P (C n) = 2 * μ (D n) := by
    calc
      P (C n) = 2 * P {ω | 1 < B (T n) ω} :=
        hB.reflection_principle one_pos (T n)
      _ = 2 * μ (D n) := by rw [htail n]
  have hTmono : Monotone T := by
    intro n m hnm
    rw [← NNReal.coe_le_coe]
    change c n ^ 2 ≤ c m ^ 2
    have hcm : c n ≤ c m := by
      dsimp only [c]
      exact_mod_cast Nat.succ_le_succ hnm
    nlinarith only [hcm, (hcpos n).le, (hcpos m).le]
  have hCmono : Monotone C := by
    intro n m hnm ω hω
    obtain ⟨t, ht, hBt⟩ := hω
    exact ⟨t, ht.trans (hTmono hnm), hBt⟩
  have hCmeas (n : ℕ) : MeasurableSet (C n) := by
    have heq : C n =
        {ω | ENNReal.ofReal 1 < denseRunningSupremum B (T n) ω} := by
      ext ω
      exact (lt_denseRunningSupremum_iff_exists_of_continuous
        (show (0 : ℝ) ≤ 1 by norm_num) (hc ω)).symm
    rw [heq]
    exact measurableSet_denseRunningSupremum_gt hm (T n) 1
  have htC : Tendsto (fun n ↦ P (C n)) atTop (𝓝 1) := by
    simpa only [hCmeasure] using ht2D
  let U : Set Ω := ⋃ n, C n
  have hPU : P U = 1 := by
    have h := tendsto_measure_iUnion_atTop (μ := P) hCmono
    change Tendsto (fun n ↦ P (C n)) atTop (𝓝 (P U)) at h
    exact tendsto_nhds_unique h htC
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion hCmeas
  have hUc : P Uᶜ = 0 := by
    calc
      P Uᶜ = P Set.univ - P U := measure_compl hUmeas (measure_ne_top P U)
      _ = 0 := by rw [hPU, measure_univ, tsub_self]
  rw [ae_iff]
  apply measure_mono_null _ hUc
  intro ω hω
  have htop : hittingAfter B (Ioi 1) 0 ω = ⊤ := by
    simpa only [mem_ofPred_eq, not_ne_iff] using hω
  show ω ∈ Uᶜ
  rw [mem_compl_iff]
  intro hωU
  obtain ⟨n, hn⟩ := mem_iUnion.mp hωU
  obtain ⟨t, _, hBt⟩ := hn
  have hle : hittingAfter B (Ioi 1) (0 : ℝ≥0) ω ≤ t :=
    hittingAfter_le_of_mem (u := B) (s := Ioi 1) (n := (0 : ℝ≥0)) bot_le hBt
  rw [htop] at hle
  exact (not_le_of_gt (WithTop.coe_lt_top t)) hle

/-- A finite first strict crossing of level one by a continuous path starting
at zero has terminal value exactly one. -/
theorem stoppedValue_hittingAfter_Ioi_one_eq_one
    (hc : Continuous (B · ω)) (hzero : B 0 ω = 0)
    (hfinite : hittingAfter B (Ioi 1) 0 ω ≠ ⊤) :
    stoppedValue B (hittingAfter B (Ioi 1) 0) ω = 1 := by
  let τ : Ω → WithTop ℝ≥0 := hittingAfter B (Ioi 1) 0
  let r : ℝ≥0 := (τ ω).untopA
  have hcoe : (r : WithTop ℝ≥0) = τ ω := by
    dsimp only [r]
    rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
  have hlower : 1 ≤ B r ω := by
    have hmem := hittingAfter_mem_closure_of_rightContinuous
      (fun t ↦ hc.continuousWithinAt) hfinite
    change B r ω ∈ closure (Ioi (1 : ℝ)) at hmem
    simpa only [closure_Ioi, mem_Ici] using hmem
  have hrpos : 0 < r := by
    apply bot_lt_iff_ne_bot.mpr
    intro hr
    change r = 0 at hr
    rw [hr, hzero] at hlower
    norm_num at hlower
  have hrclosure : r ∈ closure (Iio r) := by
    rw [closure_Iio' (a := r) ⟨(0 : ℝ≥0), hrpos⟩]
    exact mem_Iic.mpr le_rfl
  have hupper : B r ω ≤ 1 := by
    apply closure_minimal (s := Iio r) (t := {u | B u ω ≤ 1}) _
      (isClosed_le hc continuous_const) hrclosure
    intro t ht
    change B t ω ≤ 1
    apply not_lt.mp
    intro hBt
    have hlt : (t : WithTop ℝ≥0) < τ ω := by
      rw [← hcoe]
      exact WithTop.coe_lt_coe.mpr ht
    exact notMem_of_lt_hittingAfter hlt bot_le hBt
  change B r ω = 1
  exact le_antisymm hupper hlower

variable {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
  [IsProbabilityMeasure P]

/-- The abstract contradiction behind Exercise 21.10.3.  No Brownian fact is
used here: any zero-initial continuous local martingale which stops at a
nonzero constant at an almost surely finite stopping time must have a
nonintegrable normalized bracket there. -/
theorem IsContinuousLocalMartingale.not_integrable_klenkeSquareVariation_at_of_constant
    (hM : IsContinuousLocalMartingale B F P) (hF : F.IsUsual P)
    (hzero : B 0 = 0) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {a : ℝ} (ha : a ≠ 0)
    (hterminal : stoppedValue B τ =ᵐ[P] fun _ ↦ a) :
    ¬ Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) P := by
  intro hQ
  let Q : ℝ≥0 → Ω → ℝ := hM.klenkeSquareVariation hF
  let ρ : ℕ → FiniteStoppingTime F := fun n ↦
    FiniteStoppingTime.truncate hτ (n : ℝ≥0)
  let V : ℕ → Ω → ℝ := fun n ω ↦ B (ρ n ω) ω
  have hQmeas (t : ℝ≥0) : Measurable (Q t) :=
    (hM.adapted_klenkeSquareVariation hF t).mono (F.le t) le_rfl
  have hQrc : HasRightContinuousPaths Q P :=
    ae_of_all P fun ω t ↦ (hM.continuous_klenkeSquareVariation hF ω).continuousWithinAt
  have hQρ (n : ℕ) : Integrable (fun ω ↦ Q (ρ n ω) ω) P := by
    apply hQ.mono' ((ρ n).aemeasurable_sample_of_rightContinuous hQmeas hQrc
      |>.aestronglyMeasurable)
    filter_upwards [hfinite] with ω hω
    have hρτtop : ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
      change (ρ n).withTop ω ≤ τ ω
      rw [FiniteStoppingTime.withTop_truncate]
      exact min_le_right _ _
    have hτcoe : (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop hω, WithTop.coe_untop]
    have hρτ : ρ n ω ≤ (τ ω).untopA := by
      apply WithTop.coe_le_coe.mp
      rw [hτcoe]
      exact hρτtop
    have hnonneg : 0 ≤ Q (ρ n ω) ω := by
      calc
        (0 : ℝ) = Q 0 ω := (hM.klenkeSquareVariation_zero hF ω).symm
        _ ≤ Q (ρ n ω) ω := hM.monotone_klenkeSquareVariation hF ω bot_le
    change ‖Q (ρ n ω) ω‖ ≤ Q (τ ω).untopA ω
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hM.monotone_klenkeSquareVariation hF ω hρτ
  have hQρle (n : ℕ) :
      (∫ ω, Q (ρ n ω) ω ∂P) ≤ ∫ ω, Q (τ ω).untopA ω ∂P := by
    apply integral_mono_ae (hQρ n) hQ
    filter_upwards [hfinite] with ω hω
    have hρτtop : ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
      change (ρ n).withTop ω ≤ τ ω
      rw [FiniteStoppingTime.withTop_truncate]
      exact min_le_right _ _
    have hτcoe : (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop hω, WithTop.coe_untop]
    apply hM.monotone_klenkeSquareVariation hF ω
    apply WithTop.coe_le_coe.mp
    rw [hτcoe]
    exact hρτtop
  have h0Lp : MemLp (B 0) 2 P := by
    rw [hzero]
    exact MemLp.zero'
  have hL (n : ℕ) :=
    hM.squareIntegrable_stoppedProcess_and_secondMoment_le hF h0Lp (ρ n) (hQρ n)
  have heval (n : ℕ) :
      MeasureTheory.stoppedProcess B (ρ n).withTop (n : ℝ≥0) = V n := by
    funext ω
    rw [FiniteStoppingTime.stoppedProcess_eq]
    change B (min (n : ℝ≥0) (ρ n ω)) ω = B (ρ n ω) ω
    rw [min_eq_right (FiniteStoppingTime.truncate_le hτ (n : ℝ≥0) ω)]
  have hVLp (n : ℕ) : MemLp (V n) 2 P := by
    rw [← heval n]
    exact (hL n).1.2 (n : ℝ≥0)
  have hQnonneg : 0 ≤ ∫ ω, Q (τ ω).untopA ω ∂P :=
    integral_nonneg fun ω ↦ by
      calc
        (0 : ℝ) = Q 0 ω := (hM.klenkeSquareVariation_zero hF ω).symm
        _ ≤ Q (τ ω).untopA ω := hM.monotone_klenkeSquareVariation hF ω bot_le
  have hVbound (n : ℕ) :
      (∫ ω, V n ω ^ 2 ∂P) ≤ ∫ ω, Q (τ ω).untopA ω ∂P := by
    have h := (hL n).2 (n : ℝ≥0)
    rw [heval n] at h
    have hzeroInt : (∫ ω, B 0 ω ^ 2 ∂P) = 0 := by
      rw [hzero]
      simp
    rw [hzeroInt, zero_add] at h
    exact h.trans (hQρle n)
  let C : ℝ≥0 := ⟨∫ ω, Q (τ ω).untopA ω ∂P, hQnonneg⟩
  have hVUI : UniformIntegrable V 1 P :=
    uniformIntegrable_of_bounded_integral_sq hVLp C hVbound
  have hVlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ V n ω) atTop (𝓝 a) := by
    filter_upwards [hfinite, hterminal] with ω hτω hterm
    lift τ ω to ℝ≥0 using hτω with t ht
    obtain ⟨N, hN⟩ := exists_nat_ge t
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    intro n hn
    have htn : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
    have hρ : ρ n ω = t := by
      have hρtop : (((ρ n ω : ℝ≥0) : WithTop ℝ≥0)) =
          min ((n : ℝ≥0) : WithTop ℝ≥0) (τ ω) := by
        change (ρ n).withTop ω = _
        simpa only [ρ] using
          congrFun (FiniteStoppingTime.withTop_truncate hτ (n : ℝ≥0)) ω
      apply WithTop.coe_injective
      rw [hρtop, ← ht, min_eq_right htn]
    have hterm' : B t ω = a := by
      change B (τ ω).untopA ω = a at hterm
      rw [← ht, WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe] at hterm
      exact hterm
    change B (ρ n ω) ω = a
    rw [hρ, hterm']
  have haLp : MemLp (fun _ : Ω ↦ a) 1 P := memLp_const a
  have hL1 : Tendsto (fun n ↦ eLpNorm (V n - fun _ : Ω ↦ a) 1 P)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n ↦ (hVLp n).aestronglyMeasurable) haLp hVUI.2.1 hVlim
  have hInt : Tendsto (fun n ↦ ∫ ω, V n ω ∂P) atTop (𝓝 a) := by
    have h := tendsto_integral_of_L1' (fun _ : Ω ↦ a)
      haLp.aestronglyMeasurable
      (Eventually.of_forall fun n ↦ (hVLp n).integrable one_le_two) hL1
    simpa using h
  have hVmean (n : ℕ) : (∫ ω, V n ω ∂P) = 0 := by
    have hmean := hM.integrable_finiteStoppingTime_value_and_integral_eq_initial
      hF (h0Lp.integrable one_le_two) (ρ n) (hQρ n)
    change (∫ ω, V n ω ∂P) = 0
    simpa only [V, hzero, Pi.zero_apply, integral_zero] using hmean.2
  have hzeroTendsto : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 a) := by
    simpa only [hVmean] using hInt
  have : (0 : ℝ) = a := tendsto_nhds_unique tendsto_const_nhds hzeroTendsto
  exact ha this.symm

/-- Source-facing Brownian form of Klenke Exercise 21.10.3. -/
theorem IsBrownianReal.klenke_21_10_3
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) (hzero : B 0 = 0)
    (hM : IsContinuousLocalMartingale B F P) (hF : F.IsUsual P) :
    let τ := hittingAfter B (Ioi 1) 0
    IsStoppingTime F τ ∧
      (∀ᵐ ω ∂P, τ ω ≠ ⊤) ∧
      (stoppedValue B τ =ᵐ[P] fun _ ↦ (1 : ℝ)) ∧
      Integrable (fun ω ↦ stoppedValue B τ ω ^ 2) P ∧
      (∫ ω, stoppedValue B τ ω ^ 2 ∂P) = 1 ∧
      (¬ Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) P) ∧
      ((fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) =ᵐ[P]
        fun ω ↦ ((τ ω).untopA : ℝ)) ∧
      (∫⁻ ω, ENNReal.ofReal
        (hM.klenkeSquareVariation hF (τ ω).untopA ω) ∂P) = ∞ := by
  let τ := hittingAfter B (Ioi 1) 0
  letI : F.IsRightContinuous := hF.rightContinuous
  have hτ : IsStoppingTime F τ :=
    hM.1.1.isStoppingTime_hittingAfter_isOpen
      (fun ω t ↦ (hc ω).continuousWithinAt) isOpen_Ioi 0
  have hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤ :=
    hB.ae_hittingAfter_Ioi_one_ne_top hm hc
  have hterminal : stoppedValue B τ =ᵐ[P] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hfinite] with ω hω
    exact stoppedValue_hittingAfter_Ioi_one_eq_one (hc ω) (congrFun hzero ω) hω
  have hsq : (fun ω ↦ stoppedValue B τ ω ^ 2) =ᵐ[P] fun _ ↦ (1 : ℝ) :=
    hterminal.mono fun ω hω ↦ by
      calc
        stoppedValue B τ ω ^ 2 = (1 : ℝ) ^ 2 :=
          congrArg (fun x : ℝ ↦ x ^ 2) hω
        _ = 1 := by norm_num
  have hsqi : Integrable (fun ω ↦ stoppedValue B τ ω ^ 2) P :=
    (integrable_const (1 : ℝ)).congr hsq.symm
  have hsqmean : (∫ ω, stoppedValue B τ ω ^ 2 ∂P) = 1 := by
    rw [integral_congr_ae hsq]
    simp
  have hQnot :
      ¬ Integrable (fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) P :=
    hM.not_integrable_klenkeSquareVariation_at_of_constant hF hzero hτ hfinite
      one_ne_zero hterminal
  have hraw := hB.quadraticVariation_eq_time_of_semimartingale
    (hM.isSemimartingale hF) hF
  have hnormalized := hM.klenkeSquareVariation_eq_raw_sub_initial hF
  have hQtime : Indistinguishable (hM.klenkeSquareVariation hF)
      (fun t _ ↦ (t : ℝ)) P := by
    filter_upwards [hnormalized, hraw] with ω hn hr t
    rw [hn t, hr t, congrFun hzero ω]
    norm_num
  have hQτ : (fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) =ᵐ[P]
      fun ω ↦ ((τ ω).untopA : ℝ) :=
    hQtime.mono fun ω hω ↦ hω (τ ω).untopA
  have htmeas : AEStronglyMeasurable (fun ω ↦ ((τ ω).untopA : ℝ)) P :=
    have hτm : Measurable τ := hτ.measurable.mono hτ.measurableSpace_le le_rfl
    (NNReal.continuous_coe.measurable.comp hτm.untopA).aestronglyMeasurable
  have hQmeas : AEStronglyMeasurable
      (fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω) P :=
    htmeas.congr hQτ.symm
  have hQnonneg : 0 ≤ᵐ[P]
      fun ω ↦ hM.klenkeSquareVariation hF (τ ω).untopA ω :=
    ae_of_all P fun ω ↦ by
      calc
        (0 : ℝ) = hM.klenkeSquareVariation hF 0 ω :=
          (hM.klenkeSquareVariation_zero hF ω).symm
        _ ≤ hM.klenkeSquareVariation hF (τ ω).untopA ω :=
          hM.monotone_klenkeSquareVariation hF ω bot_le
  have hQinf : (∫⁻ ω, ENNReal.ofReal
      (hM.klenkeSquareVariation hF (τ ω).untopA ω) ∂P) = ∞ := by
    apply not_ne_iff.mp
    intro hne
    exact hQnot ((lintegral_ofReal_ne_top_iff_integrable hQmeas hQnonneg).mp hne)
  exact ⟨hτ, hfinite, hterminal, hsqi, hsqmean, hQnot, hQτ, hQinf⟩

namespace BrownianReal

/-- The project-owned Brownian coordinate recentered pointwise at time zero.
Unlike the raw continuous representative, this process starts at zero on every
sample point, not merely almost surely. -/
noncomputable def klenkeExerciseProcess : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  fun t ω ↦ brownianCoordinate t ω - brownianCoordinate 0 ω

theorem measurable_klenkeExerciseProcess (t : ℝ≥0) :
    Measurable (klenkeExerciseProcess t) :=
  (measurable_brownianCoordinate t).sub (measurable_brownianCoordinate 0)

theorem continuous_klenkeExerciseProcess (ω : ℝ≥0 → ℝ) :
    Continuous (klenkeExerciseProcess · ω) :=
  (continuous_brownianCoordinate ω).sub continuous_const

@[simp] theorem klenkeExerciseProcess_zero : klenkeExerciseProcess 0 = 0 := by
  funext ω
  simp only [klenkeExerciseProcess, sub_self, Pi.zero_apply]

theorem isBrownianReal_klenkeExerciseProcess :
    IsBrownianReal klenkeExerciseProcess preBrownianMeasure := by
  change IsBrownianReal
    (fun t ω ↦ brownianCoordinate t ω - brownianCoordinate 0 ω)
    preBrownianMeasure
  simpa only [zero_add] using isBrownianReal_brownianCoordinate.shift 0

/-- The natural usual augmentation used by the concrete exercise witness. -/
noncomputable def klenkeExerciseFiltration :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace
        (NullMeasurableSpace (ℝ≥0 → ℝ) preBrownianMeasure)) :=
  (Filtration.natural klenkeExerciseProcess
    (fun t ↦ (measurable_klenkeExerciseProcess t).stronglyMeasurable)).usualAugmentation
      preBrownianMeasure

/-- The same process on the completed Brownian sample space. -/
noncomputable def completedKlenkeExerciseProcess :
    ℝ≥0 → NullMeasurableSpace (ℝ≥0 → ℝ) preBrownianMeasure → ℝ :=
  fun t ω ↦ klenkeExerciseProcess t ω

theorem isContinuousLocalMartingale_completedKlenkeExerciseProcess :
    IsContinuousLocalMartingale completedKlenkeExerciseProcess klenkeExerciseFiltration
      preBrownianMeasure.completion := by
  exact isBrownianReal_klenkeExerciseProcess
    |>.isContinuousLocalMartingale_natural_usualAugmentation
      measurable_klenkeExerciseProcess

/-- A concrete first-passage time in the project-owned model. -/
noncomputable def klenkeExerciseStoppingTime :
    NullMeasurableSpace (ℝ≥0 → ℝ) preBrownianMeasure → WithTop ℝ≥0 :=
  hittingAfter completedKlenkeExerciseProcess (Ioi 1) 0

/-- Fully concrete realization of Klenke Exercise 21.10.3. -/
theorem klenke_21_10_3_counterexample :
    IsStoppingTime klenkeExerciseFiltration klenkeExerciseStoppingTime ∧
      (∀ᵐ ω ∂preBrownianMeasure.completion,
        klenkeExerciseStoppingTime ω ≠ ⊤) ∧
      (stoppedValue completedKlenkeExerciseProcess klenkeExerciseStoppingTime
        =ᵐ[preBrownianMeasure.completion] fun _ ↦ (1 : ℝ)) ∧
      Integrable (fun ω ↦ stoppedValue completedKlenkeExerciseProcess
        klenkeExerciseStoppingTime ω ^ 2) preBrownianMeasure.completion ∧
      (∫ ω, stoppedValue completedKlenkeExerciseProcess
        klenkeExerciseStoppingTime ω ^ 2 ∂preBrownianMeasure.completion) = 1 ∧
      (¬ Integrable (fun ω ↦
        isContinuousLocalMartingale_completedKlenkeExerciseProcess.klenkeSquareVariation
          (Filtration.natural klenkeExerciseProcess
            (fun t ↦ (measurable_klenkeExerciseProcess t).stronglyMeasurable)
            |>.usualAugmentation_isUsual preBrownianMeasure)
          (klenkeExerciseStoppingTime ω).untopA ω)
        preBrownianMeasure.completion) ∧
      ((fun ω ↦
        isContinuousLocalMartingale_completedKlenkeExerciseProcess.klenkeSquareVariation
          (Filtration.natural klenkeExerciseProcess
            (fun t ↦ (measurable_klenkeExerciseProcess t).stronglyMeasurable)
            |>.usualAugmentation_isUsual preBrownianMeasure)
          (klenkeExerciseStoppingTime ω).untopA ω)
          =ᵐ[preBrownianMeasure.completion]
        fun ω ↦ ((klenkeExerciseStoppingTime ω).untopA : ℝ)) ∧
      (∫⁻ ω, ENNReal.ofReal
        (isContinuousLocalMartingale_completedKlenkeExerciseProcess.klenkeSquareVariation
          (Filtration.natural klenkeExerciseProcess
            (fun t ↦ (measurable_klenkeExerciseProcess t).stronglyMeasurable)
            |>.usualAugmentation_isUsual preBrownianMeasure)
          (klenkeExerciseStoppingTime ω).untopA ω)
        ∂preBrownianMeasure.completion) = ∞ := by
  have hproc : completedKlenkeExerciseProcess =
      (fun t (ω : NullMeasurableSpace (ℝ≥0 → ℝ) preBrownianMeasure) ↦
        klenkeExerciseProcess t ω) := rfl
  have hB : IsBrownianReal completedKlenkeExerciseProcess
      preBrownianMeasure.completion := by
    simpa only [hproc] using isBrownianReal_klenkeExerciseProcess.completion
  let hM := isContinuousLocalMartingale_completedKlenkeExerciseProcess
  let hF := (Filtration.natural klenkeExerciseProcess
    (fun t ↦ (measurable_klenkeExerciseProcess t).stronglyMeasurable)
    |>.usualAugmentation_isUsual preBrownianMeasure)
  simpa only [hproc, klenkeExerciseStoppingTime, klenkeExerciseFiltration] using
    hB.klenke_21_10_3
      (fun t ↦ (measurable_klenkeExerciseProcess t).nullMeasurable.measurable')
      (fun ω ↦ continuous_klenkeExerciseProcess ω)
      klenkeExerciseProcess_zero hM hF

end BrownianReal

end ProbabilityTheory
