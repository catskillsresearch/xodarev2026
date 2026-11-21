/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Classical
public import StochLean.Probability.Process.LocalMartingale.Localization
public import StochLean.Probability.Process.UCP.CadlagConsistentLocalization

/-! # Patching consistent classical decompositions

Classical decompositions with merely adapted finite-variation parts are not
unique.  Consequently arbitrary witnesses chosen independently on successive
deterministic horizons need not be stopped-consistent.  This module isolates
the exact compatibility needed for patching: consistent local martingale and
finite-variation components on the deterministic horizons `n + 1`.

The components are patched by cadlag UCP completion.  Recovery after every
deterministic stop gives local martingality of the global martingale component,
local finite variation of the global finite-variation component, and the
global decomposition identity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

def deterministicClassicalLocalizer (n : ℕ) (_ : Ω) : WithTop ℝ≥0 :=
  (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)

omit [IsProbabilityMeasure P] in
private theorem deterministicClassicalLocalizer_isLocalizingSequence :
    IsLocalizingSequence F (deterministicClassicalLocalizer (Ω := Ω)) P := by
  refine ⟨⟨fun n ↦ isStoppingTime_const F ((n + 1 : ℕ) : ℝ≥0), ?_⟩, ?_⟩
  · exact ae_of_all _ fun _ ↦ WithTop.tendsto_coe_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).comp (tendsto_add_atTop_nat 1))
  · exact ae_of_all _ fun _ n m hnm ↦ WithTop.coe_le_coe.mpr
      (Nat.cast_le.mpr (Nat.add_le_add_right hnm 1))

private structure StoppedClassicalDecomposition
    (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (τ : Ω → WithTop ℝ≥0) where
  martingalePart : ℝ≥0 → Ω → ℝ
  finiteVariationPart : ℝ≥0 → Ω → ℝ
  isLocalMartingale : IsLocalMartingale martingalePart F P
  finiteVariation_adapted : Adapted F finiteVariationPart
  finiteVariation_cadlag : HasCadlagPaths finiteVariationPart P
  finiteVariation : HasFiniteVariationPaths finiteVariationPart P
  martingale_zero : martingalePart 0 =ᵐ[P] 0
  finiteVariation_zero : finiteVariationPart 0 =ᵐ[P] 0
  decomposition : Indistinguishable (stoppedProcess X τ)
    ((fun _ ↦ X 0) + martingalePart + finiteVariationPart) P
  martingale_stopped : stoppedProcess martingalePart τ = martingalePart
  finiteVariation_stopped : stoppedProcess finiteVariationPart τ = finiteVariationPart

private noncomputable def stoppedClassicalDecomposition
    {τ : Ω → WithTop ℝ≥0}
    (hX : IsClassicalSemimartingale (stoppedProcess X τ) F P)
    (hF : F.IsUsual P) (hτ : IsStoppingTime F τ) :
    StoppedClassicalDecomposition X F P τ := by
  let M := hX.2.2.choose
  let A := hX.2.2.choose_spec.choose
  have hs := hX.2.2.choose_spec.choose_spec
  have hM : IsLocalMartingale M F P := hs.1
  have haA : Adapted F A := hs.2.1
  have hcA : HasCadlagPaths A P := hs.2.2.1
  have hvA : HasFiniteVariationPaths A P := hs.2.2.2.1
  have hM0 : M 0 =ᵐ[P] 0 := hs.2.2.2.2.1
  have hA0 : A 0 =ᵐ[P] 0 := hs.2.2.2.2.2.1
  have hdec : Indistinguishable (stoppedProcess X τ)
      ((fun _ ↦ stoppedProcess X τ 0) + M + A) P := hs.2.2.2.2.2.2
  let MS := stoppedProcess M τ
  let AS := stoppedProcess A τ
  have hMS : IsLocalMartingale MS F P := hM.stoppedProcess hF hτ
  have haAS : Adapted F AS :=
    (haA.stronglyAdapted.stoppedProcess_of_usual hF hcA.hasRightContinuousPaths hτ).adapted
  have hcAS : HasCadlagPaths AS P := hcA.stoppedProcess τ
  have hvAS : HasFiniteVariationPaths AS P := hvA.stoppedProcess τ
  have hMS0 : MS 0 =ᵐ[P] 0 := by
    filter_upwards [hM0] with ω hω
    change stoppedProcess M τ 0 ω = 0
    rw [stoppedProcess_eq_of_le bot_le]
    exact hω
  have hAS0 : AS 0 =ᵐ[P] 0 := by
    filter_upwards [hA0] with ω hω
    change stoppedProcess A τ 0 ω = 0
    rw [stoppedProcess_eq_of_le bot_le]
    exact hω
  have hinit : stoppedProcess X τ 0 = X 0 := by
    funext ω
    exact stoppedProcess_eq_of_le bot_le
  have hdecS : Indistinguishable (stoppedProcess X τ)
      ((fun _ ↦ X 0) + MS + AS) P := by
    have hs := hdec.stoppedProcess τ
    simpa only [stoppedProcess_stoppedProcess, inf_idem, stoppedProcess_add,
      stoppedProcess_const, hinit, MS, AS] using hs
  exact ⟨MS, AS, hMS, haAS, hcAS, hvAS, hMS0, hAS0, hdecS,
    by simp only [MS, stoppedProcess_stoppedProcess, inf_idem],
    by simp only [AS, stoppedProcess_stoppedProcess, inf_idem]⟩

private noncomputable def alignedClassicalMartingalePart
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n)) :
    ℕ → ℝ≥0 → Ω → ℝ
  | 0 => (D 0).martingalePart
  | n + 1 => (D (n + 1)).martingalePart +
      (alignedClassicalMartingalePart D n -
        stoppedProcess (D (n + 1)).martingalePart (τ n))

private theorem alignedClassicalMartingalePart_isLocalMartingale
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hF : F.IsUsual P) (hτ : ∀ n, IsStoppingTime F (τ n)) :
    ∀ n, IsLocalMartingale (alignedClassicalMartingalePart D n) F P := by
  intro n
  induction n with
  | zero => exact (D 0).isLocalMartingale
  | succ n ih =>
      exact (D (n + 1)).isLocalMartingale.add
        (ih.sub ((D (n + 1)).isLocalMartingale.stoppedProcess hF (hτ n)) hF) hF

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalMartingalePart_stopped
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) : ∀ n,
    stoppedProcess (alignedClassicalMartingalePart D n) (τ n) =
      alignedClassicalMartingalePart D n := by
  intro n
  induction n with
  | zero => exact (D 0).martingale_stopped
  | succ n ih =>
      have hsmall : τ n ≤ τ (n + 1) := hmono (Nat.le_succ n)
      have hprev : stoppedProcess (alignedClassicalMartingalePart D n) (τ (n + 1)) =
          alignedClassicalMartingalePart D n := by
        calc
          stoppedProcess (alignedClassicalMartingalePart D n) (τ (n + 1)) =
              stoppedProcess
                (stoppedProcess (alignedClassicalMartingalePart D n) (τ n))
                (τ (n + 1)) := by rw [ih]
          _ = stoppedProcess (alignedClassicalMartingalePart D n) (τ n) :=
            stoppedProcess_stoppedProcess_of_le_left hsmall
          _ = alignedClassicalMartingalePart D n := ih
      change stoppedProcess
        ((D (n + 1)).martingalePart +
          (alignedClassicalMartingalePart D n -
            stoppedProcess (D (n + 1)).martingalePart (τ n))) (τ (n + 1)) = _
      rw [stoppedProcess_add, stoppedProcess_sub, (D (n + 1)).martingale_stopped,
        hprev, stoppedProcess_stoppedProcess_of_le_left hsmall]
      rfl

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalMartingalePart_stopped_consistency
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) {n m : ℕ} (hnm : n ≤ m) :
    stoppedProcess (alignedClassicalMartingalePart D m) (τ n) =
      alignedClassicalMartingalePart D n := by
  have hself := alignedClassicalMartingalePart_stopped D hmono
  have hadj (k : ℕ) :
      stoppedProcess (alignedClassicalMartingalePart D (k + 1)) (τ k) =
        alignedClassicalMartingalePart D k := by
    change stoppedProcess
      ((D (k + 1)).martingalePart +
        (alignedClassicalMartingalePart D k -
          stoppedProcess (D (k + 1)).martingalePart (τ k))) (τ k) = _
    rw [stoppedProcess_add, stoppedProcess_sub, hself k,
      stoppedProcess_stoppedProcess, inf_idem]
    ext t ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  induction m, hnm using Nat.le_induction with
  | base => exact hself n
  | succ m hnm ih =>
      have hle : τ n ≤ τ m := hmono hnm
      calc
        stoppedProcess (alignedClassicalMartingalePart D (m + 1)) (τ n) =
            stoppedProcess
              (stoppedProcess (alignedClassicalMartingalePart D (m + 1)) (τ m))
              (τ n) := by
                rw [stoppedProcess_stoppedProcess_of_le_right hle]
        _ = stoppedProcess (alignedClassicalMartingalePart D m) (τ n) := by rw [hadj]
        _ = alignedClassicalMartingalePart D n := ih

private noncomputable def alignedClassicalCorrection
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  alignedClassicalMartingalePart D n - (D n).martingalePart

private noncomputable def alignedClassicalFiniteVariationPart
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (D n).finiteVariationPart - alignedClassicalCorrection D n

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalMartingalePart_zero
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n)) :
    ∀ n, alignedClassicalMartingalePart D n 0 =ᵐ[P] 0 := by
  intro n
  induction n with
  | zero => exact (D 0).martingale_zero
  | succ n ih =>
      filter_upwards [(D (n + 1)).martingale_zero, ih] with ω hn hprev
      change (D (n + 1)).martingalePart 0 ω +
        (alignedClassicalMartingalePart D n 0 ω -
          stoppedProcess (D (n + 1)).martingalePart (τ n) 0 ω) = 0
      rw [stoppedProcess_eq_of_le bot_le, hn, hprev]
      simp only [Pi.zero_apply]
      ring

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalFiniteVariationPart_zero
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (n : ℕ) : alignedClassicalFiniteVariationPart D n 0 =ᵐ[P] 0 := by
  filter_upwards [(D n).finiteVariation_zero,
    alignedClassicalMartingalePart_zero D n, (D n).martingale_zero]
      with ω hB hM hN
  simp only [alignedClassicalFiniteVariationPart, alignedClassicalCorrection,
    Pi.sub_apply, hB, hM, hN, Pi.zero_apply, sub_self]

private theorem alignedClassicalFiniteVariationPart_adapted
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hF : F.IsUsual P) (hτ : ∀ n, IsStoppingTime F (τ n))
    (n : ℕ) : Adapted F (alignedClassicalFiniteVariationPart D n) :=
  (D n).finiteVariation_adapted.sub
    ((alignedClassicalMartingalePart_isLocalMartingale D hF hτ n).1.sub
      (D n).isLocalMartingale.1)

private theorem alignedClassicalFiniteVariationPart_cadlag
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hF : F.IsUsual P) (hτ : ∀ n, IsStoppingTime F (τ n))
    (n : ℕ) : HasCadlagPaths (alignedClassicalFiniteVariationPart D n) P :=
  (D n).finiteVariation_cadlag.sub
    ((alignedClassicalMartingalePart_isLocalMartingale D hF hτ n).2.1.sub
      (D n).isLocalMartingale.2.1)

omit [IsProbabilityMeasure P] in
private theorem alignedClassical_decomposition
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (n : ℕ) : Indistinguishable (stoppedProcess X (τ n))
      ((fun _ ↦ X 0) + alignedClassicalMartingalePart D n +
        alignedClassicalFiniteVariationPart D n) P := by
  apply (D n).decomposition.trans
  filter_upwards with ω t
  simp only [alignedClassicalFiniteVariationPart, alignedClassicalCorrection,
    Pi.add_apply, Pi.sub_apply]
  ring

omit [IsProbabilityMeasure P] in
private theorem stoppedClassicalDecomposition_overlap
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) {n m : ℕ} (hnm : n ≤ m) :
    Indistinguishable (stoppedProcess X (τ n))
      ((fun _ ↦ X 0) + stoppedProcess (D m).martingalePart (τ n) +
        stoppedProcess (D m).finiteVariationPart (τ n)) P := by
  have hs := (D m).decomposition.stoppedProcess (τ n)
  simpa only [stoppedProcess_stoppedProcess_of_le_right (hmono hnm),
    stoppedProcess_add, stoppedProcess_const] using hs

omit [IsProbabilityMeasure P] in
private theorem hasFiniteVariationPaths_sub
    {U V : ℝ≥0 → Ω → ℝ} (hU : HasFiniteVariationPaths U P)
    (hV : HasFiniteVariationPaths V P) : HasFiniteVariationPaths (U - V) P := by
  filter_upwards [hU, hV] with ω hUω hVω
  exact StochLean.locallyBoundedVariationOn_sub hUω hVω

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalCorrection_finiteVariation
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) :
    ∀ n, HasFiniteVariationPaths (alignedClassicalCorrection D n) P := by
  intro n
  induction n with
  | zero =>
      have heq : alignedClassicalCorrection D 0 = 0 := by
        ext t ω
        simp only [alignedClassicalCorrection, alignedClassicalMartingalePart,
          Pi.sub_apply, sub_self, Pi.zero_apply]
      rw [heq]
      exact Eventually.of_forall fun _ ↦
        (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  | succ n ih =>
      have hvA : HasFiniteVariationPaths (alignedClassicalFiniteVariationPart D n) P :=
        hasFiniteVariationPaths_sub (D n).finiteVariation ih
      have hvR : HasFiniteVariationPaths
          (stoppedProcess (D (n + 1)).finiteVariationPart (τ n) -
            alignedClassicalFiniteVariationPart D n) P :=
        hasFiniteVariationPaths_sub
          ((D (n + 1)).finiteVariation.stoppedProcess (τ n)) hvA
      have heCorr : Indistinguishable
          (alignedClassicalMartingalePart D n -
            stoppedProcess (D (n + 1)).martingalePart (τ n))
          (stoppedProcess (D (n + 1)).finiteVariationPart (τ n) -
            alignedClassicalFiniteVariationPart D n) P := by
        filter_upwards [alignedClassical_decomposition D n,
          stoppedClassicalDecomposition_overlap D hmono (Nat.le_succ n)]
            with ω halign hraw t
        have h₁ := halign t
        have h₂ := hraw t
        simp only [Pi.add_apply] at h₁ h₂
        simp only [Pi.sub_apply]
        linarith
      have heq : alignedClassicalCorrection D (n + 1) =
          alignedClassicalMartingalePart D n -
            stoppedProcess (D (n + 1)).martingalePart (τ n) := by
        ext t ω
        simp only [alignedClassicalCorrection, alignedClassicalMartingalePart,
          Pi.add_apply, Pi.sub_apply]
        ring
      rw [heq]
      exact HasFiniteVariationPaths.congr heCorr.symm hvR

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalFiniteVariationPart_finiteVariation
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) (n : ℕ) :
    HasFiniteVariationPaths (alignedClassicalFiniteVariationPart D n) P :=
  hasFiniteVariationPaths_sub (D n).finiteVariation
    (alignedClassicalCorrection_finiteVariation D hmono n)

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalFiniteVariationPart_stopped
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) (n : ℕ) :
    stoppedProcess (alignedClassicalFiniteVariationPart D n) (τ n) =
      alignedClassicalFiniteVariationPart D n := by
  have hM := alignedClassicalMartingalePart_stopped D hmono n
  change stoppedProcess
    ((D n).finiteVariationPart -
      (alignedClassicalMartingalePart D n - (D n).martingalePart)) (τ n) = _
  rw [stoppedProcess_sub, stoppedProcess_sub, (D n).finiteVariation_stopped,
    hM, (D n).martingale_stopped]
  rfl

omit [IsProbabilityMeasure P] in
private theorem alignedClassicalFiniteVariationPart_stopped_consistency
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (D : ∀ n, StoppedClassicalDecomposition X F P (τ n))
    (hmono : Monotone τ) {n m : ℕ} (hnm : n ≤ m) :
    Indistinguishable
      (stoppedProcess (alignedClassicalFiniteVariationPart D m) (τ n))
      (alignedClassicalFiniteVariationPart D n) P := by
  have hstopDec : Indistinguishable (stoppedProcess X (τ n))
      ((fun _ ↦ X 0) +
        stoppedProcess (alignedClassicalMartingalePart D m) (τ n) +
        stoppedProcess (alignedClassicalFiniteVariationPart D m) (τ n)) P := by
    have hs := (alignedClassical_decomposition D m).stoppedProcess (τ n)
    simpa only [stoppedProcess_stoppedProcess_of_le_right (hmono hnm),
      stoppedProcess_add, stoppedProcess_const] using hs
  have hM := alignedClassicalMartingalePart_stopped_consistency D hmono hnm
  filter_upwards [alignedClassical_decomposition D n, hstopDec]
      with ω hnω hmω t
  have h₁ := hnω t
  have h₂ := hmω t
  have h₃ := congrFun (congrFun hM t) ω
  simp only [Pi.add_apply] at h₁ h₂
  linarith

/-- Consistent classical decompositions on the deterministic horizons `n + 1`
patch to a classical decomposition on the whole half-line.

The stopped-consistency assumptions are essential for these particular
witnesses: the adapted finite-variation part in `IsClassicalSemimartingale` is
not required to be predictable, so classical decomposition witnesses are not
unique in general. -/
theorem isClassicalSemimartingale_of_consistent_deterministic_decompositions
    (haX : Adapted F X) (hcX : HasCadlagPaths X P)
    (M A : ℕ → ℝ≥0 → Ω → ℝ)
    (hM : ∀ n, IsLocalMartingale (M n) F P)
    (haA : ∀ n, Adapted F (A n))
    (hcA : ∀ n, HasCadlagPaths (A n) P)
    (hvA : ∀ n, HasFiniteVariationPaths (A n) P)
    (hM0 : ∀ n, M n 0 =ᵐ[P] 0)
    (hA0 : ∀ n, A n 0 =ᵐ[P] 0)
    (hdecomp : ∀ n, Indistinguishable
      (stoppedProcess X (deterministicClassicalLocalizer (Ω := Ω) n))
      ((fun _ ↦ X 0) + M n + A n) P)
    (hMcons : ∀ n m, n ≤ m → Indistinguishable
      (stoppedProcess (M m) (deterministicClassicalLocalizer (Ω := Ω) n)) (M n) P)
    (hAcons : ∀ n m, n ≤ m → Indistinguishable
      (stoppedProcess (A m) (deterministicClassicalLocalizer (Ω := Ω) n)) (A n) P)
    (hF : F.IsUsual P) : IsClassicalSemimartingale X F P := by
  let τ := deterministicClassicalLocalizer (Ω := Ω)
  have hτ : IsPreLocalizingSequence F τ P :=
    (deterministicClassicalLocalizer_isLocalizingSequence
      (F := F) (P := P)).toIsPreLocalizingSequence
  obtain ⟨MG, haMG, hcMG, hMucp, hMstop, _⟩ :=
    hτ.exists_cadlag_limit_of_stopped_consistency hF
      (fun n ↦ (hM n).1) (fun n ↦ (hM n).2.1) hMcons
  obtain ⟨AG, haAG, hcAG, hAucp, hAstop, _⟩ :=
    hτ.exists_cadlag_limit_of_stopped_consistency hF haA hcA hAcons
  have hMGcad : HasCadlagPaths MG P := Eventually.of_forall hcMG
  have hAGcad : HasCadlagPaths AG P := Eventually.of_forall hcAG
  have hMGlocal : IsLocalMartingale MG F P := by
    apply isLocalMartingale_of_locally_localMartingale hF hMGcad
    refine ⟨τ,
      deterministicClassicalLocalizer_isLocalizingSequence (F := F) (P := P), fun n ↦ ?_⟩
    have hs : IsLocalMartingale (stoppedProcess MG (τ n)) F P :=
      (hM n).congr hF
        ((haMG.stronglyAdapted.stoppedProcess_of_usual hF
          hMGcad.hasRightContinuousPaths (hτ.isStoppingTime n)).adapted)
        (hMstop n).symm
    have hmask : (fun t ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (MG t)) = MG := by
      funext t ω
      have hω : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < τ n ω} := by
        simp [τ, deterministicClassicalLocalizer]
      simp only [Set.indicator_of_mem hω]
    rw [hmask]
    exact hs
  have hAGfv : HasFiniteVariationPaths AG P := by
    rw [hasFiniteVariationPaths_iff_ae_forall_horizon]
    filter_upwards [ae_all_iff.mpr hAstop, ae_all_iff.mpr hvA] with ω hstopω hfvω T
    obtain ⟨n, hn⟩ := exists_nat_ge T
    have hn' : T ≤ ((n + 1 : ℕ) : ℝ≥0) :=
      hn.trans (Nat.cast_le.mpr (Nat.le_add_right n 1))
    have heq : EqOn (AG · ω) (A n · ω) (Icc 0 T) := by
      intro t ht
      have htτ : (t : WithTop ℝ≥0) ≤ τ n ω :=
        WithTop.coe_le_coe.mpr (ht.2.trans hn')
      have he := hstopω n t
      rw [stoppedProcess_eq_of_le htτ] at he
      exact he
    have hlocal : BoundedVariationOn (A n · ω) (Icc 0 T) := by
      simpa only [univ_inter] using hfvω n 0 T (mem_univ _) (mem_univ _)
    change eVariationOn (AG · ω) (Icc 0 T) ≠ ∞
    rw [show eVariationOn (AG · ω) (Icc 0 T) =
        eVariationOn (A n · ω) (Icc 0 T) from eVariationOn.congr heq]
    exact hlocal
  have hMG0 : MG 0 =ᵐ[P] 0 := hMucp.ae_eq_initial hM0
  have hAG0 : AG 0 =ᵐ[P] 0 := hAucp.ae_eq_initial hA0
  have hglobal : Indistinguishable X ((fun _ ↦ X 0) + MG + AG) P := by
    filter_upwards [ae_all_iff.mpr hdecomp, ae_all_iff.mpr hMstop,
      ae_all_iff.mpr hAstop] with ω hdecω hMω hAω t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hn' : t ≤ ((n + 1 : ℕ) : ℝ≥0) :=
      hn.trans (Nat.cast_le.mpr (Nat.le_add_right n 1))
    have htτ : (t : WithTop ℝ≥0) ≤ τ n ω := WithTop.coe_le_coe.mpr hn'
    have hdec := hdecω n t
    have hm := hMω n t
    have hA := hAω n t
    rw [stoppedProcess_eq_of_le htτ] at hdec hm hA
    simpa only [Pi.add_apply, hm, hA] using hdec
  exact ⟨haX, hcX, MG, AG, hMGlocal, haAG, hAGcad, hAGfv, hMG0, hAG0, hglobal⟩

/-- Classical decomposability on every deterministic compact horizon patches
to a classical decomposition on the whole half-line.

The finite-horizon witnesses may be chosen independently.  Before applying
the consistent-localization theorem, the proof recursively corrects the next
martingale part by its stopped discrepancy with the preceding aligned part;
the opposite correction is absorbed into the finite-variation part.  The
discrepancy has finite variation because the two decompositions agree on the
overlap. -/
theorem isClassicalSemimartingale_of_deterministic_stoppedProcess
    (hX : ∀ n, IsClassicalSemimartingale
      (stoppedProcess X (deterministicClassicalLocalizer (Ω := Ω) n)) F P)
    (hF : F.IsUsual P) : IsClassicalSemimartingale X F P := by
  let τ := deterministicClassicalLocalizer (Ω := Ω)
  have hτL : IsLocalizingSequence F τ P :=
    deterministicClassicalLocalizer_isLocalizingSequence (F := F) (P := P)
  have hτ : IsPreLocalizingSequence F τ P := hτL.toIsPreLocalizingSequence
  have hmono : Monotone τ := by
    intro n m hnm ω
    exact WithTop.coe_le_coe.mpr
      (Nat.cast_le.mpr (Nat.add_le_add_right hnm 1))
  have haX : Adapted F X := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hn' : t ≤ ((n + 1 : ℕ) : ℝ≥0) :=
      hn.trans (Nat.cast_le.mpr (Nat.le_add_right n 1))
    have hs := (hX n).1 t
    change Measurable[F t] (stoppedProcess X (τ n) t) at hs
    have heq : stoppedProcess X (τ n) t = X t := by
      funext ω
      exact stoppedProcess_eq_of_le (WithTop.coe_le_coe.mpr hn')
    rwa [heq] at hs
  let S : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess X (τ n)
  have hScons : ∀ n m, n ≤ m →
      Indistinguishable (stoppedProcess (S m) (τ n)) (S n) P := by
    intro n m hnm
    have heq : stoppedProcess (S m) (τ n) = S n := by
      simpa only [S] using
        (stoppedProcess_stoppedProcess_of_le_right (u := X) (hmono hnm))
    rw [heq]
    exact Indistinguishable.refl _
  obtain ⟨Y, _, hcY, _, hYstop, _⟩ :=
    hτ.exists_cadlag_limit_of_stopped_consistency hF
      (fun n ↦ (hX n).1) (fun n ↦ (hX n).2.1) hScons
  have hXY : Indistinguishable X Y P := by
    filter_upwards [ae_all_iff.mpr hYstop] with ω hω t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hn' : t ≤ ((n + 1 : ℕ) : ℝ≥0) :=
      hn.trans (Nat.cast_le.mpr (Nat.le_add_right n 1))
    have htτ : (t : WithTop ℝ≥0) ≤ τ n ω := WithTop.coe_le_coe.mpr hn'
    have he := hω n t
    change stoppedProcess Y (τ n) t ω = stoppedProcess X (τ n) t ω at he
    rw [stoppedProcess_eq_of_le htτ, stoppedProcess_eq_of_le htτ] at he
    exact he.symm
  have hcX : HasCadlagPaths X P :=
    HasCadlagPaths.congr hXY.symm (Eventually.of_forall hcY)
  let D : ∀ n, StoppedClassicalDecomposition X F P (τ n) := fun n ↦
    stoppedClassicalDecomposition (hX n) hF (hτ.isStoppingTime n)
  let M : ℕ → ℝ≥0 → Ω → ℝ := alignedClassicalMartingalePart D
  let A : ℕ → ℝ≥0 → Ω → ℝ := alignedClassicalFiniteVariationPart D
  have hM : ∀ n, IsLocalMartingale (M n) F P :=
    alignedClassicalMartingalePart_isLocalMartingale D hF hτ.isStoppingTime
  have haA : ∀ n, Adapted F (A n) := fun n ↦
    alignedClassicalFiniteVariationPart_adapted D hF hτ.isStoppingTime n
  have hcA : ∀ n, HasCadlagPaths (A n) P := fun n ↦
    alignedClassicalFiniteVariationPart_cadlag D hF hτ.isStoppingTime n
  have hvA : ∀ n, HasFiniteVariationPaths (A n) P := fun n ↦
    alignedClassicalFiniteVariationPart_finiteVariation D hmono n
  have hM0 : ∀ n, M n 0 =ᵐ[P] 0 := alignedClassicalMartingalePart_zero D
  have hA0 : ∀ n, A n 0 =ᵐ[P] 0 :=
    alignedClassicalFiniteVariationPart_zero D
  have hdec : ∀ n, Indistinguishable (stoppedProcess X (τ n))
      ((fun _ ↦ X 0) + M n + A n) P := alignedClassical_decomposition D
  have hMcons : ∀ n m, n ≤ m →
      Indistinguishable (stoppedProcess (M m) (τ n)) (M n) P := by
    intro n m hnm
    have heq := alignedClassicalMartingalePart_stopped_consistency D hmono hnm
    rw [heq]
    exact Indistinguishable.refl _
  have hAcons : ∀ n m, n ≤ m →
      Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P :=
    fun _ _ hnm ↦ alignedClassicalFiniteVariationPart_stopped_consistency D hmono hnm
  exact isClassicalSemimartingale_of_consistent_deterministic_decompositions
    haX hcX M A hM haA hcA hvA hM0 hA0 hdec hMcons hAcons hF

end ProbabilityTheory
