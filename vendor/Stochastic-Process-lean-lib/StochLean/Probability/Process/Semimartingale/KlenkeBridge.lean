/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalConstancy
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousMoments
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousCharacterization
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPart
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousLeft
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Characterization
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.GeneralLocalMartingale
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Probability.Process.LocalMartingale.ContinuousSquareLocalization
public import StochLean.Analysis.PathVariation.QuadraticVariationStieltjes
public import StochLean.Analysis.PathVariation.Restriction

/-! # Klenke's normalized continuous brackets

Klenke Section 21.10 uses brackets starting at zero, while the canonical
Protter raw square bracket contains the initial square.  These definitions are
therefore views of the already constructed continuous parts; they do not
select or construct a second stochastic quadratic variation.

The same bridge records Klenke 21.74 on its native pathwise zero-QV domain
and Exercise 21.10.2 as convergence of right-endpoint weighted square sums to
the actual pathwise Stieltjes integral.  Their continuous-local-martingale
specializations reuse the common all-times subsequence extracted below.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}
  {X Y : ℝ≥0 → Ω → ℝ}

private theorem tendstoInMeasure_sub_same {ι : Type*} {l : Filter ι}
    {f : ι → Ω → ℝ} {g c : Ω → ℝ}
    (h : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω ↦ f i ω - c ω) l (fun ω ↦ g ω - c ω) := by
  intro ε hε
  simpa only [edist_dist, dist_eq_norm, sub_sub_sub_cancel_right] using h ε hε

variable [IsFiniteMeasure P]

/-- Klenke's zero-initial square variation, implemented by the continuous
part of the unique Protter raw bracket. -/
noncomputable def IsContinuousLocalMartingale.klenkeSquareVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  (hX.isSemimartingale hF).continuousQuadraticVariation hF

/-- Klenke's zero-initial covariation, implemented by polarization of the
continuous parts of the unique Protter raw brackets. -/
noncomputable def IsContinuousLocalMartingale.klenkeCovariation
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  (hX.isSemimartingale hF).continuousQuadraticCovariation
    (hY.isSemimartingale hF) hF

theorem IsContinuousLocalMartingale.klenkeSquareVariation_zero
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.klenkeSquareVariation hF 0 ω = 0 :=
  (hX.isSemimartingale hF).continuousQuadraticVariation_zero hF ω

theorem IsContinuousLocalMartingale.adapted_klenkeSquareVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.klenkeSquareVariation hF) :=
  (hX.isSemimartingale hF).adapted_continuousQuadraticVariation hF

theorem IsContinuousLocalMartingale.continuous_klenkeSquareVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (fun t ↦ hX.klenkeSquareVariation hF t ω) :=
  (hX.isSemimartingale hF).continuous_continuousQuadraticVariation hF ω

theorem IsContinuousLocalMartingale.monotone_klenkeSquareVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Monotone (fun t ↦ hX.klenkeSquareVariation hF t ω) :=
  (hX.isSemimartingale hF).monotone_continuousQuadraticVariation hF ω

/-- Klenke 21.70(i), structural part: the normalized owner is continuous,
adapted, increasing, and starts exactly at zero. -/
theorem IsContinuousLocalMartingale.klenkeSquareVariation_properties
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.klenkeSquareVariation hF) ∧
      (∀ ω, Continuous (fun t ↦ hX.klenkeSquareVariation hF t ω)) ∧
      (∀ ω, Monotone (fun t ↦ hX.klenkeSquareVariation hF t ω)) ∧
      hX.klenkeSquareVariation hF 0 = 0 := by
  refine ⟨hX.adapted_klenkeSquareVariation hF,
    hX.continuous_klenkeSquareVariation hF,
    hX.monotone_klenkeSquareVariation hF, ?_⟩
  funext ω
  exact hX.klenkeSquareVariation_zero hF ω

/-- The compatibility identity required by the single-owner rule: Klenke's
bracket is the raw bracket minus its initial square. -/
theorem IsContinuousLocalMartingale.klenkeSquareVariation_eq_raw_sub_initial
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.klenkeSquareVariation hF)
      (fun t ω ↦ (hX.isSemimartingale hF).quadraticVariation hF t ω -
        (X 0 ω) ^ 2) P :=
  (hX.isSemimartingale hF).continuousQuadraticVariation_eq_of_continuous hF hX.2

/-- Klenke 21.70(i), martingale part.  The source-normalized bracket starts
at zero, so the raw compensated square is corrected by the time-constant
initial square.  The native local-martingale mask makes no unnecessary
integrability assumption on `X 0`. -/
theorem IsContinuousLocalMartingale.isLocalMartingale_sq_sub_klenkeSquareVariation
    [IsProbabilityMeasure P]
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsLocalMartingale
      (fun t ω ↦ (X t ω) ^ 2 - hX.klenkeSquareVariation hF t ω) F P := by
  have hraw := hX.1.isLocalMartingale_sq_sub_quadraticVariation hF
  have hinit := (isContinuousLocalMartingale_const_initial (P := P) (F := F)
    ((hX.1.1 0).pow_const 2)).1
  apply (hraw.add hinit hF).congr hF
    (fun t ↦ ((hX.1.1 t).pow_const 2).sub
      (hX.adapted_klenkeSquareVariation hF t))
  filter_upwards [hX.klenkeSquareVariation_eq_raw_sub_initial hF] with ω hω t
  simp only [Pi.add_apply, Pi.sub_apply, hω t]
  ring

/-- Klenke 21.70(i), continuity bundled with the compensated-square
local-martingale assertion. -/
theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_sq_sub_klenkeSquareVariation
    [IsProbabilityMeasure P]
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsContinuousLocalMartingale
      (fun t ω ↦ (X t ω) ^ 2 - hX.klenkeSquareVariation hF t ω) F P := by
  refine ⟨hX.isLocalMartingale_sq_sub_klenkeSquareVariation hF, ?_⟩
  filter_upwards [hX.2] with ω hXω
  exact (hXω.pow 2).sub (hX.continuous_klenkeSquareVariation hF ω)

variable [SigmaFiniteFiltration P F]

/-- Klenke 21.70(i), normalized candidate uniqueness.  A zero-initial
continuous finite-variation candidate is translated by the initial square,
identified by raw quadratic-variation uniqueness, and translated back. -/
theorem IsContinuousLocalMartingale.klenkeSquareVariation_unique
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    {A : ℝ≥0 → Ω → ℝ} (ha : Adapted F A)
    (hc : HasContinuousPaths A P) (hv : HasFiniteVariationPaths A P)
    (hM : IsLocalMartingale ((fun t ω ↦ (X t ω) ^ 2) - A) F P)
    (h0 : A 0 =ᵐ[P] 0) :
    Indistinguishable A (hX.klenkeSquareVariation hF) P := by
  let C : ℝ≥0 → Ω → ℝ := fun _ ω ↦ (X 0 ω) ^ 2
  let hC : IsContinuousLocalMartingale C F P :=
    isContinuousLocalMartingale_const_initial ((hX.1.1 0).pow_const 2)
  let B := A + C
  have haB : Adapted F B := fun t ↦ (ha t).add (hC.1.1 t)
  have hcB : HasContinuousPaths B P := by
    filter_upwards [hc, hC.2] with ω haω hcω
    exact haω.add hcω
  have hvC : HasFiniteVariationPaths C P := by
    exact ae_of_all P fun ω ↦
      ((show Monotone (C · ω) from monotone_const).monotoneOn
        Set.univ).locallyBoundedVariationOn
  have hvB : HasFiniteVariationPaths B P := by
    filter_upwards [hv, hvC] with ω haω hcω
    exact StochLean.locallyBoundedVariationOn_add haω hcω
  have hMraw : IsLocalMartingale ((fun t ω ↦ (X t ω) ^ 2) - B) F P := by
    apply (hM.sub hC.1 hF).congr hF
      (fun t ↦ ((hX.1.1 t).pow_const 2).sub (haB t))
    exact Eventually.of_forall fun ω t ↦ by
      simp only [B, C, Pi.sub_apply, Pi.add_apply]
      ring
  have h0B : B 0 =ᵐ[P] fun ω ↦ (X 0 ω) ^ 2 := by
    filter_upwards [h0] with ω hAω
    simp only [B, C, Pi.add_apply, hAω, Pi.zero_apply, zero_add]
  have hraw := hX.quadraticVariation_eq_of_sq_sub_localMartingale hF
    haB hcB hvB hMraw h0B
  filter_upwards [hraw, hX.klenkeSquareVariation_eq_raw_sub_initial hF]
    with ω hrawω hnormω t
  calc
    A t ω = B t ω - (X 0 ω) ^ 2 := by
      simp only [B, C, Pi.add_apply]
      ring
    _ = (hX.isSemimartingale hF).quadraticVariation hF t ω - (X 0 ω) ^ 2 := by
      rw [hrawω t]
    _ = hX.klenkeSquareVariation hF t ω := (hnormω t).symm

/-- Klenke 21.72: zero normalized square variation is equivalent to being
indistinguishable from the time-constant initial process. -/
theorem IsContinuousLocalMartingale.klenkeSquareVariation_zero_iff_constant
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.klenkeSquareVariation hF) 0 P ↔
      Indistinguishable X (fun _ ↦ X 0) P := by
  rw [← hX.quadraticVariation_eq_initial_iff_constant hF]
  constructor
  · intro hzero
    filter_upwards [hX.klenkeSquareVariation_eq_raw_sub_initial hF, hzero]
      with ω hnorm hz t
    have ht := hnorm t
    rw [hz t] at ht
    simp only [Pi.zero_apply] at ht
    linarith
  · intro hraw
    filter_upwards [hX.klenkeSquareVariation_eq_raw_sub_initial hF, hraw]
      with ω hnorm hr t
    rw [hnorm t, hr t]
    simp only [Pi.zero_apply, sub_self]

theorem IsContinuousLocalMartingale.klenkeCovariation_zero
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.klenkeCovariation hY hF 0 ω = 0 :=
  (hX.isSemimartingale hF).continuousQuadraticCovariation_zero
    (hY.isSemimartingale hF) hF ω

/-- Klenke 21.73, structural part.  Mixed covariation is continuous and of
locally finite variation, but is deliberately not typed as increasing. -/
theorem IsContinuousLocalMartingale.klenkeCovariation_properties
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    Adapted F (hX.klenkeCovariation hY hF) ∧
      HasContinuousPaths (hX.klenkeCovariation hY hF) P ∧
      HasFiniteVariationPaths (hX.klenkeCovariation hY hF) P ∧
      hX.klenkeCovariation hY hF 0 = 0 := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  refine ⟨hSX.adapted_continuousQuadraticCovariation hSY hF,
    hSX.hasContinuousPaths_continuousQuadraticCovariation hSY hF,
    hSX.hasFiniteVariationPaths_continuousQuadraticCovariation hSY hF, ?_⟩
  funext ω
  exact hX.klenkeCovariation_zero hY hF ω

/-- The single-owner compatibility identity for mixed brackets.  Continuity
of either factor removes all positive-time mixed jumps; the only difference
between the raw Protter covariation and Klenke's normalized covariation is the
initial product. -/
theorem IsContinuousLocalMartingale.klenkeCovariation_eq_raw_sub_initial
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.klenkeCovariation hY hF)
      (fun t ω ↦ (hX.isSemimartingale hF).quadraticCovariation
        (hY.isSemimartingale hF) hF t ω - X 0 ω * Y 0 ω) P :=
  (hX.isSemimartingale hF).continuousQuadraticCovariation_eq_of_left_continuous
    (hY.isSemimartingale hF) hF hX.2

/-- Klenke 21.73, martingale characterization.  No integrability assumption
on the initial product is needed in the native masked local-martingale
semantics. -/
theorem IsContinuousLocalMartingale.isLocalMartingale_mul_sub_klenkeCovariation
    [IsProbabilityMeasure P]
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsLocalMartingale
      (fun t ω ↦ X t ω * Y t ω - hX.klenkeCovariation hY hF t ω) F P := by
  have hraw := hX.1.isLocalMartingale_mul_sub_quadraticCovariation hY.1 hF
  have hinit := (isContinuousLocalMartingale_const_initial (P := P) (F := F)
    ((hX.1.1 0).mul (hY.1.1 0))).1
  apply (hraw.add hinit hF).congr hF
    (fun t ↦ ((hX.1.1 t).mul (hY.1.1 t)).sub
      ((hX.isSemimartingale hF).adapted_continuousQuadraticCovariation
        (hY.isSemimartingale hF) hF t))
  filter_upwards [hX.klenkeCovariation_eq_raw_sub_initial hY hF] with ω hω t
  change X t ω * Y t ω -
      (hX.isSemimartingale hF).quadraticCovariation
        (hY.isSemimartingale hF) hF t ω + X 0 ω * Y 0 ω =
    X t ω * Y t ω - hX.klenkeCovariation hY hF t ω
  rw [hω t]
  ring

/-- Klenke 21.73, continuity bundled with the compensated-product
local-martingale assertion. -/
theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_mul_sub_klenkeCovariation
    [IsProbabilityMeasure P]
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsContinuousLocalMartingale
      (fun t ω ↦ X t ω * Y t ω - hX.klenkeCovariation hY hF t ω) F P := by
  refine ⟨hX.isLocalMartingale_mul_sub_klenkeCovariation hY hF, ?_⟩
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  filter_upwards [hX.2, hY.2] with ω hXω hYω
  exact (hXω.mul hYω).sub
    (hSX.continuous_continuousQuadraticCovariation hSY hF ω)

/-- Klenke 21.73, normalized mixed-covariation candidate uniqueness.  The
zero-initial candidate is translated by the initial product before applying
the raw mixed-bracket uniqueness theorem. -/
theorem IsContinuousLocalMartingale.klenkeCovariation_unique
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P)
    {A : ℝ≥0 → Ω → ℝ} (ha : Adapted F A)
    (hc : HasContinuousPaths A P) (hv : HasFiniteVariationPaths A P)
    (hM : IsLocalMartingale ((fun t ω ↦ X t ω * Y t ω) - A) F P)
    (h0 : A 0 =ᵐ[P] 0) :
    Indistinguishable A (hX.klenkeCovariation hY hF) P := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  let C : ℝ≥0 → Ω → ℝ := fun _ ω ↦ X 0 ω * Y 0 ω
  let hC : IsContinuousLocalMartingale C F P :=
    isContinuousLocalMartingale_const_initial ((hX.1.1 0).mul (hY.1.1 0))
  let B := A + C
  have haB : Adapted F B := fun t ↦ (ha t).add (hC.1.1 t)
  have hcB : HasContinuousPaths B P := by
    filter_upwards [hc, hC.2] with ω haω hcω
    exact haω.add hcω
  have hvC : HasFiniteVariationPaths C P := by
    exact ae_of_all P fun ω ↦
      ((show Monotone (C · ω) from monotone_const).monotoneOn
        Set.univ).locallyBoundedVariationOn
  have hvB : HasFiniteVariationPaths B P := by
    filter_upwards [hv, hvC] with ω haω hcω
    exact StochLean.locallyBoundedVariationOn_add haω hcω
  have hMraw : IsLocalMartingale ((fun t ω ↦ X t ω * Y t ω) - B) F P := by
    apply (hM.sub hC.1 hF).congr hF
      (fun t ↦ ((hX.1.1 t).mul (hY.1.1 t)).sub (haB t))
    exact Eventually.of_forall fun ω t ↦ by
      simp only [B, C, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      ring
  have hjB : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 →
      jumpProcess B t ω = jumpProcess X t ω * jumpProcess Y t ω := by
    filter_upwards [hcB, hX.2, hY.2] with ω hBω hXω hYω
    intro t ht
    rw [hBω.jumpProcess_eq_zero ht, hXω.jumpProcess_eq_zero ht,
      hYω.jumpProcess_eq_zero ht, zero_mul]
  have h0B : B 0 =ᵐ[P] fun ω ↦ X 0 ω * Y 0 ω := by
    filter_upwards [h0] with ω hAω
    simp only [B, C, Pi.add_apply, hAω, Pi.zero_apply, zero_add]
  have hraw := hSX.quadraticCovariation_unique_of_locally_squareIntegrable hSY hF
    (hX.locally_squareIntegrableMartingale hF)
    (hY.locally_squareIntegrableMartingale hF) haB hcB.hasCadlagPaths hvB hMraw hjB h0B
  filter_upwards [hraw, hX.klenkeCovariation_eq_raw_sub_initial hY hF]
    with ω hrawω hnormω t
  calc
    A t ω = B t ω - X 0 ω * Y 0 ω := by
      simp only [B, C, Pi.add_apply]
      ring
    _ = hSX.quadraticCovariation hSY hF t ω - X 0 ω * Y 0 ω := by
      rw [hrawω t]
    _ = hX.klenkeCovariation hY hF t ω := (hnormω t).symm

/-- Klenke 21.70(ii): along every deterministic admissible partition
sequence, the square-increment sums on a fixed finite horizon converge in
probability to the normalized continuous bracket.  The auxiliary Protter
partition uses growing horizons; exact finite restriction then removes the
raw initial square. -/
theorem IsContinuousLocalMartingale.tendstoInMeasure_klenkeSquareVariationSum
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    (T : ℝ≥0) :
    TendstoInMeasure P
      (fun n ω ↦ quadraticVariationSum ((π n).restrict T) (X · ω)) atTop
      (hX.klenkeSquareVariation hF T) := by
  let ρ : ℕ → StoppingTimePartition F := fun n ↦
    StoppingTimePartition.deterministic F ((π n).restrict n)
  have hρ : StoppingTimePartition.IsTendingToIdentity ρ P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke hπ
      tendsto_natCast_atTop_atTop
  have hraw := ((hX.isSemimartingale hF).tendstoUCP_quadraticVariationSumProcess
    hF hρ).fixedTime T
  have htranslated := tendstoInMeasure_sub_same (c := fun ω ↦ (X 0 ω) ^ 2) hraw
  refine TendstoInMeasure.congr' ?_ ?_ htranslated
  · filter_upwards [
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop)
        |>.eventually (eventually_ge_atTop T)] with n hn
    exact ae_of_all P fun ω ↦ by
      change ((X 0 ω) ^ 2 + quadraticVariationSum ((π n).restrict n)
        (fun s ↦ X (min s T) ω)) - (X 0 ω) ^ 2 =
          quadraticVariationSum ((π n).restrict T) (X · ω)
      rw [(π n).quadraticVariationSum_restrict_eq_stop hn (X · ω)]
      ring
  · exact (hX.klenkeSquareVariation_eq_raw_sub_initial hF).ae_eq T |>.symm

/-- Klenke 21.73, partition characterization of mixed covariation. -/
theorem IsContinuousLocalMartingale.tendstoInMeasure_klenkeCovariationSum
    (hX : IsContinuousLocalMartingale X F P)
    (hY : IsContinuousLocalMartingale Y F P) (hF : F.IsUsual P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    (T : ℝ≥0) :
    TendstoInMeasure P
      (fun n ω ↦ covariationSum ((π n).restrict T) (X · ω) (Y · ω)) atTop
      (hX.klenkeCovariation hY hF T) := by
  let ρ : ℕ → StoppingTimePartition F := fun n ↦
    StoppingTimePartition.deterministic F ((π n).restrict n)
  have hρ : StoppingTimePartition.IsTendingToIdentity ρ P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke hπ
      tendsto_natCast_atTop_atTop
  have hraw := ((hX.isSemimartingale hF).tendstoUCP_quadraticCovariationSumProcess
    (hY.isSemimartingale hF) hF hρ).fixedTime T
  have htranslated := tendstoInMeasure_sub_same (c := fun ω ↦ X 0 ω * Y 0 ω) hraw
  refine TendstoInMeasure.congr' ?_ ?_ htranslated
  · filter_upwards [
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0)) atTop atTop)
        |>.eventually (eventually_ge_atTop T)] with n hn
    exact ae_of_all P fun ω ↦ by
      change (X 0 ω * Y 0 ω + covariationSum ((π n).restrict n)
        (fun s ↦ X (min s T) ω) (fun s ↦ Y (min s T) ω)) - X 0 ω * Y 0 ω =
          covariationSum ((π n).restrict T) (X · ω) (Y · ω)
      rw [(π n).covariationSum_restrict_eq_stop hn (X · ω) (Y · ω)]
      ring
  · exact (hX.klenkeCovariation_eq_raw_sub_initial hY hF).ae_eq T |>.symm

/-- Corrected Klenke 21.71.  A single subsequence works almost surely for
every finite time.  The proof does not use the false monotonicity claim for
partial-cell square sums: UCP supplies a locally-uniform subsequence, while
the exact restriction identity transports its values back to the original
infinite deterministic partitions. -/
theorem IsContinuousLocalMartingale.exists_seq_ae_klenkeSquareVariationAlong
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        HasQuadraticVariationAlong (fun n ↦ (π (k n)).restrict T)
          (X · ω) (hX.klenkeSquareVariation hF T ω) := by
  let ρ : ℕ → StoppingTimePartition F := fun n ↦
    StoppingTimePartition.deterministic F ((π n).restrict n)
  have hρ : StoppingTimePartition.IsTendingToIdentity ρ P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke hπ
      tendsto_natCast_atTop_atTop
  obtain ⟨k, hk, hU⟩ :=
    ((hX.isSemimartingale hF).tendstoUCP_quadraticVariationSumProcess
      hF hρ).exists_seq_ae_locallyUniform
  refine ⟨k, hk, ?_⟩
  filter_upwards [hU, hX.klenkeSquareVariation_eq_raw_sub_initial hF]
    with ω hu hnorm
  intro T
  have hpoint : Tendsto
      (fun n ↦ (ρ (k n)).quadraticVariationSumProcess X T ω) atTop
      (𝓝 ((hX.isSemimartingale hF).quadraticVariation hF T ω)) := by
    rw [tendsto_iff_edist_tendsto_0]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T)
    · intro n
      exact bot_le
    · intro n
      change edist ((ρ (k n)).quadraticVariationSumProcess X T ω)
        ((hX.isSemimartingale hF).quadraticVariation hF T ω) ≤
          compactDeviation ((ρ (k n)).quadraticVariationSumProcess X)
            ((hX.isSemimartingale hF).quadraticVariation hF) T ω
      simpa only [edist_dist, dist_eq_norm_sub] using
        (enorm_sub_le_compactDeviation
          (X := (ρ (k n)).quadraticVariationSumProcess X)
          (Y := (hX.isSemimartingale hF).quadraticVariation hF) le_rfl ω)
  have htranslated := hpoint.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (X 0 ω) ^ 2) atTop (𝓝 ((X 0 ω) ^ 2)))
  rw [hnorm T]
  apply htranslated.congr'
  filter_upwards [
      ((tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop) :
        Tendsto (fun n ↦ (k n : ℝ≥0)) atTop atTop).eventually
          (eventually_ge_atTop T)] with n hn
  change T ≤ (k n : ℝ≥0) at hn
  change ((X 0 ω) ^ 2 + quadraticVariationSum ((π (k n)).restrict (k n))
      (fun s ↦ X (min s T) ω)) - (X 0 ω) ^ 2 =
    quadraticVariationSum ((π (k n)).restrict T) (X · ω)
  rw [(π (k n)).quadraticVariationSum_restrict_eq_stop hn (X · ω)]
  ring

/-- Klenke 21.74 in its full native pathwise domain.  Adding a path whose
quadratic variation along the same partitions is zero does not change the
quadratic-variation limit.  The perturbation `A` is only a path here; in
particular, no semimartingale structure is assumed. -/
theorem klenke_21_74
    {T : ℝ≥0} {π : ℕ → TimePartition T} {M A : ℝ≥0 → ℝ} {q : ℝ}
    (hM : HasQuadraticVariationAlong π M q)
    (hA : HasQuadraticVariationAlong π A 0) :
    HasQuadraticVariationAlong π (M + A) q :=
  hM.add_zero hA

/-- Klenke 21.74 specialized to the canonical normalized square variation of
a continuous local martingale.  A single subsequence works for every finite
time on one common event.  The perturbation still needs only pathwise zero
quadratic variation along the original admissible sequence. -/
theorem IsContinuousLocalMartingale.exists_seq_ae_klenkeSquareVariationAlong_add_zero
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (A : ℝ≥0 → Ω → ℝ) {π : ℕ → LocallyFinitePartition}
    (hπ : IsAdmissiblePartitionSequence π)
    (hA : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) (A · ω) 0) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        HasQuadraticVariationAlong (fun n ↦ (π (k n)).restrict T)
          ((X · ω) + (A · ω)) (hX.klenkeSquareVariation hF T ω) := by
  obtain ⟨k, hk, hXqv⟩ := hX.exists_seq_ae_klenkeSquareVariationAlong hF hπ
  refine ⟨k, hk, ?_⟩
  filter_upwards [hXqv, hA] with ω hXω hAω
  intro T
  exact klenke_21_74 (hXω T) ((hAω T).comp hk.tendsto_atTop)

/-- Klenke Exercise 21.10.2.  For a continuous path with continuous
quadratic-variation limit along an admissible partition sequence, the sums
weighted at the right endpoints converge to the actual Stieltjes integral
against that limit. -/
theorem klenke_exercise_21_10_2
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    {x Q f : ℝ≥0 → ℝ} (hx : Continuous x) (hQcont : Continuous Q)
    (hQ : ∀ T : ℝ≥0,
      HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) x (Q T))
    (hf : Continuous f) (T : ℝ≥0) :
    Tendsto (fun n ↦ ∑ i : Fin ((π n).restrict T).size,
      f (((π n).restrict T).right i) * (((π n).restrict T).increment x i) ^ 2) atTop
      (𝓝 (pathStieltjesIntegral Q
        (locallyBoundedVariationOn_quadraticVariation_restrict_limit hx
          (fun S ↦ NNReal.continuous_coe.continuousAt.tendsto.comp
            (hπ.restrict_mesh_tendsto (fun _ ↦ S))) hQ)
        (fun _ ↦ hQcont.continuousWithinAt) f T)) := by
  apply tendsto_weightedQuadraticVariationSum_right
    (hx := hx.continuousOn)
    (hm := NNReal.continuous_coe.continuousAt.tendsto.comp
      (hπ.restrict_mesh_tendsto (fun _ ↦ T)))
    (hQ := fun s _ ↦ hQ s)
    (hf := hf.continuousOn)

/-- Continuous-local-martingale specialization of Klenke Exercise 21.10.2.
After the common all-times extraction, every continuous deterministic weight
has the right-endpoint weighted square-sum limit given by integration against
the canonical normalized bracket. -/
theorem IsContinuousLocalMartingale.exists_seq_ae_tendsto_klenkeWeightedQuadraticVariationSum
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        Tendsto (fun n ↦ ∑ i : Fin ((π (k n)).restrict T).size,
          f (((π (k n)).restrict T).right i) *
            (((π (k n)).restrict T).increment (X · ω) i) ^ 2) atTop
          (𝓝 (pathStieltjesIntegral (hX.klenkeSquareVariation hF · ω)
            ((hX.monotone_klenkeSquareVariation hF ω).monotoneOn
              Set.univ).locallyBoundedVariationOn
            (fun _ ↦ (hX.continuous_klenkeSquareVariation hF ω).continuousWithinAt)
            f T)) := by
  obtain ⟨k, hk, hQ⟩ := hX.exists_seq_ae_klenkeSquareVariationAlong hF hπ
  refine ⟨k, hk, ?_⟩
  have hπk : IsAdmissiblePartitionSequence (fun n ↦ π (k n)) :=
    ⟨hπ.1.comp hk.monotone, hπ.2.comp hk.tendsto_atTop⟩
  filter_upwards [hQ, hX.2] with ω hQω hXω
  intro T
  exact klenke_exercise_21_10_2 hπk hXω
    (hX.continuous_klenkeSquareVariation hF ω) hQω hf T

end ProbabilityTheory
