/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousDensityLocalization
public import StochLean.Probability.Process.FiniteVariation.StoppedJumpStep
public import StochLean.Probability.Process.LocalMartingale.NonnegativeZero
public import StochLean.Probability.Process.LocalMartingale.NonnegativePredictableJump
public import StochLean.Probability.Process.LocalMartingale.Stability
public import StochLean.Probability.Process.Stopping.PredictableLimitPart
public import StochLean.Probability.Process.Stopping.Restriction
public import StochLean.Probability.Process.Stopping.Supremum

/-! # The density-killing time under one-way absolute continuity

The increasing lower-density exits converge to a raw extinction time.  The
Lenglart killing time is its restriction to the event where the density has a
strictly positive left limit.  Thus continuous extinction is excluded, while
a jump from a positive left limit to zero is retained.  Under the target law
the time is almost surely infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- Supremum of the geometric lower-density exits.  On a good nonnegative
càdlàg density path this is its first extinction time. -/
noncomputable def absoluteContinuousDensityExtinctionTime
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨆ n : ℕ, absoluteContinuousDensityExit Q P F n ω

/-- The source left limit of the density at its raw extinction time, with an
explicit zero value when the time is infinite. -/
noncomputable def absoluteContinuousDensityExtinctionLeft
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (ω : Ω) : ℝ :=
  stoppedValueWithTerminal (leftLimitProcess (densityProcess Q P F))
    (fun _ ↦ (0 : ℝ)) (absoluteContinuousDensityExtinctionTime Q P F) ω

/-- Protter's density-killing time: retain raw extinction only when the
density has a strictly positive left limit there. -/
noncomputable def absoluteContinuousDensityKillingTime
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) : Ω → WithTop ℝ≥0 :=
  restrictedStoppingTime (absoluteContinuousDensityExtinctionTime Q P F)
    {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω}

/-- The raw extinction time is a stopping time as a countable supremum of
the increasing geometric exits. -/
theorem isStoppingTime_absoluteContinuousDensityExtinctionTime
    (hF : F.IsUsual P) :
    IsStoppingTime F (absoluteContinuousDensityExtinctionTime Q P F) := by
  exact IsStoppingTime.iSup_nnreal
    (fun n ↦ isStoppingTime_absoluteContinuousDensityExit (Q := Q) hF n)

/-- The positive-left-limit restriction is measurable at the raw extinction
time, so the killing time is itself a stopping time. -/
theorem isStoppingTime_absoluteContinuousDensityKillingTime
    (hF : F.IsUsual P) :
    IsStoppingTime F (absoluteContinuousDensityKillingTime Q P F) := by
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let hR : IsStoppingTime F R :=
    isStoppingTime_absoluteContinuousDensityExtinctionTime (Q := Q) hF
  have hm : StronglyMeasurable[hR.measurableSpaceBefore]
      (absoluteContinuousDensityExtinctionLeft Q P F) := by
    change StronglyMeasurable[hR.measurableSpaceBefore]
      (stoppedValueWithTerminal (leftLimitProcess (densityProcess Q P F))
        (fun _ ↦ (0 : ℝ)) R)
    exact (martingale_densityProcess (Q := Q) hF).stronglyAdapted.adapted
      |>.stronglyMeasurable_stopped_leftLimit_of_usual hF
        (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)) hR
  have hEbefore : MeasurableSet[hR.measurableSpaceBefore]
      {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} :=
    measurableSet_lt measurable_const hm.measurable
  exact hR.restrictedStoppingTime
    (hR.measurableSpaceBefore_le _ hEbefore)

/-- The killing time is strictly positive pointwise; a zero raw time has zero
left limit and is removed by the restriction. -/
theorem absoluteContinuousDensityKillingTime_pos (ω : Ω) :
    0 < absoluteContinuousDensityKillingTime Q P F ω := by
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let E := {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω}
  by_cases hE : ω ∈ E
  · rw [absoluteContinuousDensityKillingTime,
      restrictedStoppingTime_of_mem R hE]
    by_contra hnot
    have hR0 : R ω = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have hleft0 : absoluteContinuousDensityExtinctionLeft Q P F ω = 0 := by
      simp [absoluteContinuousDensityExtinctionLeft, stoppedValueWithTerminal,
        stoppedValue, R, hR0]
    have hpos : 0 < absoluteContinuousDensityExtinctionLeft Q P F ω := hE
    rw [hleft0] at hpos
    exact (lt_irrefl 0 hpos)
  · rw [absoluteContinuousDensityKillingTime,
      restrictedStoppingTime_of_notMem R hE]
    exact WithTop.coe_lt_top 0

/-- The raw extinction time is infinite under the target law. -/
theorem ae_absoluteContinuousDensityExtinctionTime_eq_top
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    absoluteContinuousDensityExtinctionTime Q P F =ᵐ[Q] (fun _ ↦ ⊤) := by
  filter_upwards [ae_tendsto_absoluteContinuousDensityExit hQP hF] with ω hω
  change (⨆ n : ℕ, absoluteContinuousDensityExit Q P F n ω) = ⊤
  apply iSup_eq_top.mpr
  intro b hb
  obtain ⟨t, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hb)
  rw [WithTop.tendsto_nhds_top_iff] at hω
  exact (hω t).exists

/-- Consequently the positive-left-limit killing time is also almost surely
infinite under the target law. -/
theorem ae_absoluteContinuousDensityKillingTime_eq_top
    (hQP : Q ≪ P) (hF : F.IsUsual P) :
    absoluteContinuousDensityKillingTime Q P F =ᵐ[Q] (fun _ ↦ ⊤) := by
  filter_upwards [ae_absoluteContinuousDensityExtinctionTime_eq_top hQP hF]
    with ω hω
  rw [absoluteContinuousDensityKillingTime]
  by_cases hE : 0 < absoluteContinuousDensityExtinctionLeft Q P F ω
  · rw [restrictedStoppingTime_of_mem _
      (show ω ∈ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} from hE), hω]
  · rw [restrictedStoppingTime_of_notMem _
      (show ω ∉ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} from hE)]

/-- A finite killing time is exactly the raw extinction time; finiteness forces
membership in the positive-left-limit restriction event. -/
theorem absoluteContinuousDensityKillingTime_eq_extinctionTime_of_ne_top
    {ω : Ω} (hfinite : absoluteContinuousDensityKillingTime Q P F ω ≠ ⊤) :
    absoluteContinuousDensityKillingTime Q P F ω =
      absoluteContinuousDensityExtinctionTime Q P F ω := by
  by_cases hE : 0 < absoluteContinuousDensityExtinctionLeft Q P F ω
  · exact restrictedStoppingTime_of_mem _
      (show ω ∈ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} from hE)
  · rw [absoluteContinuousDensityKillingTime,
      restrictedStoppingTime_of_notMem _
        (show ω ∉ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} from hE)]
      at hfinite
    exact (hfinite rfl).elim

/-- By construction, every finite killing time has a strictly positive source
left density. -/
theorem absoluteContinuousDensityExtinctionLeft_pos_of_killingTime_ne_top
    {ω : Ω} (hfinite : absoluteContinuousDensityKillingTime Q P F ω ≠ ⊤) :
    0 < absoluteContinuousDensityExtinctionLeft Q P F ω := by
  by_contra h
  have hnot : ω ∉ {ω | 0 < absoluteContinuousDensityExtinctionLeft Q P F ω} := h
  rw [absoluteContinuousDensityKillingTime,
    restrictedStoppingTime_of_notMem _ hnot] at hfinite
  exact hfinite rfl

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- If all geometric lower-density exits lie strictly below their finite
supremum, the density has left limit zero there. -/
private theorem leftLimitProcess_densityProcess_extinction_eq_zero_of_strict
    {ω : Ω} (hpath : IsCadlagPath (densityProcess Q P F · ω))
    (hnonneg : ∀ t : ℝ≥0, 0 ≤ densityProcess Q P F t ω)
    (hstrict : ∀ n, absoluteContinuousDensityExit Q P F n ω <
      absoluteContinuousDensityExtinctionTime Q P F ω)
    (hfinite : absoluteContinuousDensityExtinctionTime Q P F ω ≠ ⊤) :
    leftLimitProcess (densityProcess Q P F)
      (absoluteContinuousDensityExtinctionTime Q P F ω).untopA ω = 0 := by
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let σ := absoluteContinuousDensityExit Q P F
  let r := (R ω).untopA
  have hrpos : 0 < r := by
    apply WithTop.coe_lt_coe.mp
    rw [show (r : WithTop ℝ≥0) = R ω by
      dsimp only [r]
      rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]]
    exact lt_of_le_of_lt bot_le (hstrict 0)
  have hσfinite (n : ℕ) : σ n ω ≠ ⊤ := ne_top_of_lt (hstrict n)
  have hRlim : Tendsto (fun n ↦ σ n ω) atTop (𝓝 (R ω)) := by
    simpa only [R, σ, absoluteContinuousDensityExtinctionTime] using
      tendsto_atTop_iSup (monotone_absoluteContinuousDensityExit
        (Q := Q) (P := P) (F := F) ω)
  have htime : Tendsto (fun n ↦ (σ n ω).untopA) atTop (𝓝 r) := by
    exact (WithTop.tendsto_untopA hfinite).comp hRlim
  have hlt (n : ℕ) : (σ n ω).untopA < r := by
    apply WithTop.coe_lt_coe.mp
    rw [show ((σ n ω).untopA : WithTop ℝ≥0) = σ n ω by
      rw [WithTop.untopA_eq_untop (hσfinite n), WithTop.coe_untop],
      show (r : WithTop ℝ≥0) = R ω by
        dsimp only [r]
        rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]]
    exact hstrict n
  have htimeLeft : Tendsto (fun n ↦ (σ n ω).untopA) atTop (𝓝[<] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨htime, Eventually.of_forall hlt⟩
  have hvalueZero : Tendsto
      (fun n ↦ densityProcess Q P F (σ n ω).untopA ω) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ hnonneg _
    · exact Eventually.of_forall fun n ↦
        densityProcess_at_absoluteContinuousDensityExit_le
          (Q := Q) (P := P) (F := F) hpath.1 (hσfinite n)
    · exact tendsto_absoluteContinuousDensityThreshold_zero
  have hvalueLeft : Tendsto
      (fun n ↦ densityProcess Q P F (σ n ω).untopA ω) atTop
      (𝓝 (leftLimitProcess (densityProcess Q P F) r ω)) :=
    (hpath.tendsto_leftLimitProcess hrpos.ne').comp htimeLeft
  exact tendsto_nhds_unique hvalueLeft hvalueZero

/-- The density vanishes at every finite raw extinction time.  On the strict
limit branch, the extinction time is predictable and its nonnegative sampled
jump must vanish; on the attained branch the geometric exit bounds converge
to zero. -/
theorem ae_densityProcess_at_absoluteContinuousDensityExtinctionTime_eq_zero
    (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, absoluteContinuousDensityExtinctionTime Q P F ω ≠ ⊤ →
      densityProcess Q P F
        (absoluteContinuousDensityExtinctionTime Q P F ω).untopA ω = 0 := by
  let Z := densityProcess Q P F
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let σ := absoluteContinuousDensityExit Q P F
  let A : Set Ω := {ω | ∀ n, σ n ω < R ω}
  let τ := restrictedStoppingTime R A
  have hτpred : IsPredictableStoppingTime F τ P := by
    exact isPredictableStoppingTime_iSup_restricted_strict
      (fun n ↦ isStoppingTime_absoluteContinuousDensityExit (Q := Q) hF n)
      (fun ω ↦ monotone_absoluteContinuousDensityExit
        (Q := Q) (P := P) (F := F) ω) hF
  have hjnonneg : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → τ ω = (t : WithTop ℝ≥0) →
      0 ≤ jumpProcess Z t ω := by
    filter_upwards [hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F),
      ae_forall_densityProcess_nonneg (Q := Q) hF] with ω hpath hnonneg
    intro t ht hτt
    have hmem : ω ∈ A := by
      by_contra hnot
      have htop : τ ω = ⊤ := restrictedStoppingTime_of_notMem R hnot
      rw [htop] at hτt
      exact WithTop.top_ne_coe hτt
    have hR : R ω = (t : WithTop ℝ≥0) := by
      rw [← hτt]
      exact (restrictedStoppingTime_of_mem R hmem).symm
    have hfinite : R ω ≠ ⊤ := by rw [hR]; exact WithTop.coe_ne_top
    have huntop : (R ω).untopA = t := by
      rw [WithTop.untopA_eq_untop hfinite]
      apply WithTop.coe_injective
      rw [WithTop.coe_untop, hR]
    have hleft : leftLimitProcess Z t ω = 0 := by
      have hz := leftLimitProcess_densityProcess_extinction_eq_zero_of_strict
        (Q := Q) (P := P) (F := F) hpath hnonneg hmem hfinite
      simpa only [Z, R, huntop] using hz
    simp only [jumpProcess, Pi.sub_apply, hleft, sub_zero]
    exact hnonneg t
  let hZ : IsLocalMartingale Z F P :=
    (show IsUIMartingale Z F P from
      ⟨martingale_densityProcess hF, uniformIntegrable_densityProcess hF⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess
  have hjzero :=
    hZ.ae_jumpProcess_eq_zero_at_predictable_of_sampled_nonneg hF hτpred hjnonneg
  filter_upwards [hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F),
      ae_forall_densityProcess_nonneg (Q := Q) hF, hjzero]
    with ω hpath hnonneg hjzeroω
  intro hfinite
  by_cases hmem : ω ∈ A
  · have hRpos : 0 < R ω := lt_of_le_of_lt bot_le (hmem 0)
    have hrpos : 0 < (R ω).untopA := by
      apply WithTop.coe_lt_coe.mp
      rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
      exact hRpos
    have hτR : τ ω = R ω := restrictedStoppingTime_of_mem R hmem
    have hj : jumpProcess Z (R ω).untopA ω = 0 := by
      apply hjzeroω _ hrpos
      rw [hτR, WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
    have hleft := leftLimitProcess_densityProcess_extinction_eq_zero_of_strict
      (Q := Q) (P := P) (F := F) hpath hnonneg hmem hfinite
    change leftLimitProcess Z (R ω).untopA ω = 0 at hleft
    change Z (R ω).untopA ω = 0
    change Z (R ω).untopA ω - leftLimitProcess Z (R ω).untopA ω = 0 at hj
    rw [hleft, sub_zero] at hj
    exact hj
  · change ¬ ∀ n, σ n ω < R ω at hmem
    push Not at hmem
    obtain ⟨n, hn⟩ := hmem
    have hσle : σ n ω ≤ R ω := le_iSup (fun k : ℕ ↦ σ k ω) n
    have hσeq : σ n ω = R ω := le_antisymm hσle hn
    apply le_antisymm ?_ (hnonneg _)
    apply ge_of_tendsto tendsto_absoluteContinuousDensityThreshold_zero
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hσmEq : σ m ω = R ω := by
      apply le_antisymm (le_iSup (fun k : ℕ ↦ σ k ω) m)
      calc
        R ω = σ n ω := hσeq.symm
        _ ≤ σ m ω := monotone_absoluteContinuousDensityExit
          (Q := Q) (P := P) (F := F) ω hnm
    have hσmFinite : σ m ω ≠ ⊤ := hσmEq ▸ hfinite
    have hle := densityProcess_at_absoluteContinuousDensityExit_le
      (Q := Q) (P := P) (F := F) hpath.1 hσmFinite
    change densityProcess Q P F (σ m ω).untopA ω ≤
      (absoluteContinuousDensityThreshold m : ℝ) at hle
    rw [hσmEq] at hle
    exact hle

/-- The nonnegative density is absorbed at its raw extinction time, including
the continuous-extinction branch excluded from the killing time. -/
theorem indistinguishable_densityProcess_stopped_extinctionTime
    (hF : F.IsUsual P) :
    Indistinguishable
      (densityProcess Q P F)
      (MeasureTheory.stoppedProcess (densityProcess Q P F)
        (absoluteContinuousDensityExtinctionTime Q P F)) P := by
  let Z := densityProcess Q P F
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let hR : IsStoppingTime F R :=
    isStoppingTime_absoluteContinuousDensityExtinctionTime (Q := Q) hF
  let hZ : IsLocalMartingale Z F P :=
    (show IsUIMartingale Z F P from
      ⟨martingale_densityProcess hF, uniformIntegrable_densityProcess hF⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess
  let hZR : IsLocalMartingale (MeasureTheory.stoppedProcess Z R) F P :=
    hZ.stoppedProcess hF hR
  let Y := Z - MeasureTheory.stoppedProcess Z R
  have hY : IsLocalMartingale Y F P := hZ.sub hZR hF
  have hY0 : Y 0 =ᵐ[P] 0 := ae_of_all P fun ω ↦ by
    change Z 0 ω - MeasureTheory.stoppedProcess Z R 0 ω = 0
    rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
    ring
  have hYn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Y t ω := by
    filter_upwards [ae_forall_densityProcess_nonneg (Q := Q) hF,
      ae_densityProcess_at_absoluteContinuousDensityExtinctionTime_eq_zero
        (Q := Q) hF] with ω hnonneg hzero
    intro t
    by_cases htop : R ω = ⊤
    · change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
      simp only [MeasureTheory.stoppedProcess, htop, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe, sub_self]
      exact le_rfl
    · by_cases ht : (t : WithTop ℝ≥0) ≤ R ω
      · change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
        rw [MeasureTheory.stoppedProcess_eq_of_le ht, sub_self]
      · have hRt : R ω ≤ (t : WithTop ℝ≥0) := le_of_not_ge ht
        have hzero' : Z (R ω).untopA ω = 0 := by
          exact hzero htop
        change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
        rw [MeasureTheory.stoppedProcess_eq_of_ge hRt, hzero', sub_zero]
        exact hnonneg t
  have heY : Indistinguishable Y 0 P :=
    hY.indistinguishable_zero_of_nonneg hYn hY0
  filter_upwards [heY] with ω hω t
  change Z t ω = MeasureTheory.stoppedProcess Z R t ω
  have := hω t
  change Z t ω - MeasureTheory.stoppedProcess Z R t ω = 0 at this
  linarith

/-- On one source-full-measure event, the density is nonzero exactly strictly
before its raw extinction time. -/
theorem ae_densityProcess_ne_zero_iff_lt_extinctionTime
    (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      densityProcess Q P F t ω ≠ 0 ↔
        (t : WithTop ℝ≥0) < absoluteContinuousDensityExtinctionTime Q P F ω := by
  let Z := densityProcess Q P F
  let R := absoluteContinuousDensityExtinctionTime Q P F
  filter_upwards [indistinguishable_densityProcess_stopped_extinctionTime
      (Q := Q) hF,
    ae_densityProcess_at_absoluteContinuousDensityExtinctionTime_eq_zero
      (Q := Q) hF] with ω habs hzero
  intro t
  constructor
  · intro hne
    apply lt_of_not_ge
    intro hRt
    have hfinite : R ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hRt
    have hstop : Z t ω = Z (R ω).untopA ω := by
      have h := habs t
      change Z t ω = MeasureTheory.stoppedProcess Z R t ω at h
      rw [MeasureTheory.stoppedProcess_eq_of_ge hRt] at h
      exact h
    exact hne (hstop.trans (hzero hfinite))
  · intro ht hzeroT
    have hex : ∃ n, (t : WithTop ℝ≥0) <
        absoluteContinuousDensityExit Q P F n ω := by
      rw [absoluteContinuousDensityExtinctionTime] at ht
      exact lt_iSup_iff.mp ht
    obtain ⟨n, hn⟩ := hex
    have hle := absoluteContinuousDensityThreshold_le_of_lt_exit
      (Q := Q) (P := P) (F := F) hn
    rw [hzeroT] at hle
    exact (not_le_of_gt (show (0 : ℝ) <
      (absoluteContinuousDensityThreshold n : ℝ) by
        exact_mod_cast absoluteContinuousDensityThreshold_pos n)) hle

/-- On a nonnegative càdlàg density path, a finite positive-left-limit
extinction is a jump to zero.  The proof uses the actual geometric exits: once
they enter a left neighborhood on which the density is bounded away from
zero, every later exit must equal the extinction time, and its threshold tends
to zero. -/
theorem densityProcess_at_absoluteContinuousDensityKillingTime_eq_zero
    {ω : Ω}
    (hpath : IsCadlagPath (densityProcess Q P F · ω))
    (hnonneg : ∀ t : ℝ≥0, 0 ≤ densityProcess Q P F t ω)
    (hfinite : absoluteContinuousDensityKillingTime Q P F ω ≠ ⊤) :
    densityProcess Q P F
      (absoluteContinuousDensityKillingTime Q P F ω).untopA ω = 0 := by
  let Z := densityProcess Q P F
  let R := absoluteContinuousDensityExtinctionTime Q P F
  let K := absoluteContinuousDensityKillingTime Q P F
  have hKR : K ω = R ω :=
    absoluteContinuousDensityKillingTime_eq_extinctionTime_of_ne_top hfinite
  have hRfinite : R ω ≠ ⊤ := hKR ▸ hfinite
  let r : ℝ≥0 := (R ω).untopA
  have hRcoe : (r : WithTop ℝ≥0) = R ω := by
    dsimp only [r]
    rw [WithTop.untopA_eq_untop hRfinite, WithTop.coe_untop]
  have hKpos : 0 < K ω := absoluteContinuousDensityKillingTime_pos ω
  have hrpos : 0 < r := by
    apply WithTop.coe_lt_coe.mp
    rw [hRcoe, ← hKR]
    exact hKpos
  have hleftEq : absoluteContinuousDensityExtinctionLeft Q P F ω =
      leftLimitProcess Z r ω := by
    simp only [absoluteContinuousDensityExtinctionLeft, Z, R,
      stoppedValueWithTerminal_of_ne_top hRfinite, stoppedValue, r]
  have hleftPos : 0 < leftLimitProcess Z r ω := by
    rw [← hleftEq]
    exact absoluteContinuousDensityExtinctionLeft_pos_of_killingTime_ne_top hfinite
  have hRtendsto : Tendsto
      (fun n ↦ absoluteContinuousDensityExit Q P F n ω) atTop (𝓝 (R ω)) := by
    simpa only [R, absoluteContinuousDensityExtinctionTime] using
      (tendsto_atTop_iSup (monotone_absoluteContinuousDensityExit
        (Q := Q) (P := P) (F := F) ω))
  have hzero : Z r ω = 0 := by
    apply le_antisymm ?_ (hnonneg r)
    apply le_of_not_gt
    intro hZpos
    have hminpos : 0 < min (leftLimitProcess Z r ω) (Z r ω) :=
      lt_min hleftPos hZpos
    have hevThreshold := tendsto_absoluteContinuousDensityThreshold_zero.eventually
      (Iio_mem_nhds hminpos)
    obtain ⟨n, hn⟩ := hevThreshold.exists
    have hnLeft : (absoluteContinuousDensityThreshold n : ℝ) <
        leftLimitProcess Z r ω := hn.trans_le (min_le_left _ _)
    have hnValue : (absoluteContinuousDensityThreshold n : ℝ) < Z r ω :=
      hn.trans_le (min_le_right _ _)
    have hnearEv : ∀ᶠ s in 𝓝[<] r,
        (absoluteContinuousDensityThreshold n : ℝ) < Z s ω :=
      (hpath.tendsto_leftLimitProcess hrpos.ne').eventually
        (Ioi_mem_nhds hnLeft)
    obtain ⟨a, ha, hnear⟩ :=
      (mem_nhdsLT_iff_exists_Ioo_subset' hrpos).mp hnearEv
    have hevAbove : ∀ᶠ m : ℕ in atTop,
        (a : WithTop ℝ≥0) < absoluteContinuousDensityExit Q P F m ω :=
      hRtendsto.eventually (Ioi_mem_nhds (by
        rw [← hRcoe]
        exact WithTop.coe_lt_coe.mpr ha))
    obtain ⟨m, hmAbove, hnm⟩ :=
      (hevAbove.and (eventually_ge_atTop n)).exists
    have hRmle : absoluteContinuousDensityExit Q P F m ω ≤ R ω := by
      exact le_iSup (fun k : ℕ ↦ absoluteContinuousDensityExit Q P F k ω) m
    have hRmEq : absoluteContinuousDensityExit Q P F m ω = R ω := by
      apply le_antisymm hRmle
      apply le_of_not_gt
      intro hlt
      have hRmfinite : absoluteContinuousDensityExit Q P F m ω ≠ ⊤ :=
        ne_top_of_le_ne_top hRfinite hRmle
      let s : ℝ≥0 := (absoluteContinuousDensityExit Q P F m ω).untopA
      have hscoe : (s : WithTop ℝ≥0) =
          absoluteContinuousDensityExit Q P F m ω := by
        dsimp only [s]
        rw [WithTop.untopA_eq_untop hRmfinite, WithTop.coe_untop]
      have has : a < s := by
        apply WithTop.coe_lt_coe.mp
        rwa [hscoe]
      have hsr : s < r := by
        apply WithTop.coe_lt_coe.mp
        rwa [hscoe, hRcoe]
      have hnearValue : (absoluteContinuousDensityThreshold n : ℝ) < Z s ω :=
        hnear ⟨has, hsr⟩
      have hExitValue : Z s ω ≤ (absoluteContinuousDensityThreshold m : ℝ) := by
        simpa only [Z, s] using
          (densityProcess_at_absoluteContinuousDensityExit_le
            (Q := Q) (P := P) (F := F) hpath.1 hRmfinite)
      have hThresholdMono : (absoluteContinuousDensityThreshold m : ℝ) ≤
          (absoluteContinuousDensityThreshold n : ℝ) := by
        exact_mod_cast antitone_absoluteContinuousDensityThreshold hnm
      exact (not_lt_of_ge (hExitValue.trans hThresholdMono)) hnearValue
    have hRmfinite : absoluteContinuousDensityExit Q P F m ω ≠ ⊤ :=
      hRmEq ▸ hRfinite
    have hExitValue : Z r ω ≤ (absoluteContinuousDensityThreshold m : ℝ) := by
      have h := densityProcess_at_absoluteContinuousDensityExit_le
        (Q := Q) (P := P) (F := F) hpath.1 hRmfinite
      rw [hRmEq] at h
      simpa only [Z, r] using h
    have hThresholdMono : (absoluteContinuousDensityThreshold m : ℝ) ≤
        (absoluteContinuousDensityThreshold n : ℝ) := by
      exact_mod_cast antitone_absoluteContinuousDensityThreshold hnm
    exact (not_lt_of_ge (hExitValue.trans hThresholdMono)) hnValue
  change Z (K ω).untopA ω = 0
  rw [hKR]
  exact hzero

/-- The nonnegative density is absorbed at its killing time.  When the time
is finite its stopped value is zero; when it is infinite stopping does
nothing.  The stopped-process difference is therefore a nonnegative local
martingale starting at zero. -/
theorem indistinguishable_densityProcess_stopped_killingTime
    (hF : F.IsUsual P) :
    Indistinguishable
      (densityProcess Q P F)
      (MeasureTheory.stoppedProcess (densityProcess Q P F)
        (absoluteContinuousDensityKillingTime Q P F)) P := by
  let Z := densityProcess Q P F
  let R := absoluteContinuousDensityKillingTime Q P F
  let hR : IsStoppingTime F R :=
    isStoppingTime_absoluteContinuousDensityKillingTime (Q := Q) hF
  let hZ : IsLocalMartingale Z F P :=
    (show IsUIMartingale Z F P from
      ⟨martingale_densityProcess hF, uniformIntegrable_densityProcess hF⟩)
        |>.isLocalMartingale hasCadlagPaths_densityProcess
  let hZR : IsLocalMartingale (MeasureTheory.stoppedProcess Z R) F P :=
    hZ.stoppedProcess hF hR
  let Y := Z - MeasureTheory.stoppedProcess Z R
  have hY : IsLocalMartingale Y F P := hZ.sub hZR hF
  have hY0 : Y 0 =ᵐ[P] 0 := ae_of_all P fun ω ↦ by
    change Z 0 ω - MeasureTheory.stoppedProcess Z R 0 ω = 0
    rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
    ring
  have hYn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Y t ω := by
    filter_upwards [hZ.2.1, ae_forall_densityProcess_nonneg (Q := Q) hF]
      with ω hcad hnonneg
    intro t
    by_cases htop : R ω = ⊤
    · change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
      simp only [MeasureTheory.stoppedProcess, htop, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe, sub_self]
      exact le_rfl
    · by_cases ht : (t : WithTop ℝ≥0) ≤ R ω
      · change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
        rw [MeasureTheory.stoppedProcess_eq_of_le ht, sub_self]
      · have hRt : R ω ≤ (t : WithTop ℝ≥0) := le_of_not_ge ht
        have hzero : Z (R ω).untopA ω = 0 := by
          exact densityProcess_at_absoluteContinuousDensityKillingTime_eq_zero
            (Q := Q) (P := P) (F := F) hcad hnonneg htop
        change 0 ≤ Z t ω - MeasureTheory.stoppedProcess Z R t ω
        rw [MeasureTheory.stoppedProcess_eq_of_ge hRt, hzero, sub_zero]
        exact hnonneg t
  have heY : Indistinguishable Y 0 P :=
    hY.indistinguishable_zero_of_nonneg hYn hY0
  filter_upwards [heY] with ω hω t
  change Z t ω = MeasureTheory.stoppedProcess Z R t ω
  have := hω t
  change Z t ω - MeasureTheory.stoppedProcess Z R t ω = 0 at this
  linarith

end ProbabilityTheory
