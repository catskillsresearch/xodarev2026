/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.Regularization
public import StochLean.Probability.Martingale.Inequalities.DoobGlobalL2
public import StochLean.Probability.Moments.L2
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Maximal control from a conditional remaining-difference bound

A terminal difference alone does not control the intermediate process. The actual
conditional remaining-difference bound supplies the second term. Two conditional
martingales and the native global Doob inequality give a square-integrable envelope
for a countable family of observations. No martingale property of that family is
assumed. In particular, this can be used for left-step dyadic Doob differences.

Only the constructed cadlag conditional martingales use dense running suprema.
The observed family has its ordinary countable supremum, with finiteness proved
before conversion to real values. No UCP or maximal convergence is an input.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {D W : Ω → ℝ}

/-- An actual global L2 envelope for each coordinate of the conditional family.
The coordinatewise AE conclusion deliberately does not intersect all time indices. -/
theorem exists_memLp_two_global_condExp_envelope (hF : F.IsUsual P) (hD : MemLp D 2 P) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ‖P[D | F t] ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 4 * ∫ ω, D ω ^ 2 ∂P := by
  obtain ⟨M, hM, hcM, he, _⟩ := (martingale_condExp D F P).exists_cadlag_modification hF
  have hclose (t : ℝ≥0) : M t =ᵐ[P] P[D | F t] := (he t).symm
  have hLM (t : ℝ≥0) : MemLp (M t) 2 P :=
    (hD.condExp (by norm_num)).ae_eq (hclose t).symm
  have hbound (t : ℝ≥0) : (∫ ω, ‖M t ω‖ ^ 2 ∂P) ≤ ∫ ω, D ω ^ 2 ∂P := by
    have hnorm : eLpNorm (M t) 2 P ≤ eLpNorm D 2 P := by
      rw [eLpNorm_congr_ae (hclose t)]
      exact eLpNorm_condExp_le_eLpNorm D (by norm_num)
    simpa only [Real.norm_eq_abs, sq_abs] using
      integral_sq_le_of_eLpNorm_two_le (hLM t) hD hnorm
  obtain ⟨g, hgm, hgn, hgL, hgb, hgE⟩ :=
    hM.exists_memLp_two_globalEnvelope hcM.hasRightContinuousPaths hLM hbound
  refine ⟨g, hgm, hgn, hgL, fun t ↦ ?_, hgE⟩
  filter_upwards [hgb, hclose t] with ω hb heω
  simpa only [heω] using hb t

variable {ι : Type*} [Countable ι] {e : ι → ℝ≥0} {C : ι → Ω → ℝ}

/-- The terminal difference and its conditional remainder control all countably
many observations on one event. No ordering of the observation times is needed. -/
theorem exists_memLp_two_countable_condExp_tail_envelope
    (hF : F.IsUsual P) (hD : MemLp D 2 P) (hW : MemLp W 2 P)
    (hm : ∀ i, StronglyMeasurable[F (e i)] (C i)) (hi : ∀ i, Integrable (C i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖P[D - C i | F (e i)] ω‖ ≤ P[W | F (e i)] ω) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ i, ‖C i ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 8 * ((∫ ω, D ω ^ 2 ∂P) + ∫ ω, W ω ^ 2 ∂P) := by
  obtain ⟨gD, hmD, hnD, hLD, hbD, hED⟩ := exists_memLp_two_global_condExp_envelope hF hD
  obtain ⟨gW, hmW, hnW, hLW, hbW, hEW⟩ := exists_memLp_two_global_condExp_envelope hF hW
  have hcoordinate (i : ι) : ∀ᵐ ω ∂P, ‖C i ω‖ ≤ gD ω + gW ω := by
    have he := condExp_sub (hD.integrable (by norm_num)) (hi i) (F (e i))
    rw [condExp_of_stronglyMeasurable (F.le (e i)) (hm i) (hi i)] at he
    filter_upwards [he, hb i, hbD (e i), hbW (e i)] with ω heω hr hd hw
    have heC : C i ω = P[D | F (e i)] ω - P[D - C i | F (e i)] ω := by
      change P[D - C i | F (e i)] ω = P[D | F (e i)] ω - C i ω at heω
      linarith
    rw [heC]
    exact (norm_sub_le _ _).trans (add_le_add hd (hr.trans ((le_abs_self _).trans hw)))
  refine ⟨fun ω ↦ gD ω + gW ω, hmD.add hmW, fun ω ↦ add_nonneg (hnD ω) (hnW ω),
    hLD.add hLW, eventually_countable_forall.mpr hcoordinate, ?_⟩
  have hsq : (∫ ω, (gD ω + gW ω) ^ 2 ∂P) ≤
      ∫ ω, 2 * (gD ω ^ 2 + gW ω ^ 2) ∂P := by
    apply integral_mono_ae (hLD.add hLW).integrable_sq
      ((hLD.integrable_sq.add hLW.integrable_sq).const_mul 2)
    exact Eventually.of_forall fun ω ↦ by
      change (gD ω + gW ω) ^ 2 ≤ 2 * (gD ω ^ 2 + gW ω ^ 2)
      nlinarith [sq_nonneg (gD ω - gW ω)]
  rw [integral_const_mul, integral_add hLD.integrable_sq hLW.integrable_sq] at hsq
  linarith only [hsq, hED, hEW]

/-- The ordinary countable supremum is finite almost surely and its real value is
in L2. This is a conclusion from the two terminal inputs, not a supplied envelope. -/
theorem memLp_two_iSup_of_condExp_tail_bound
    (hF : F.IsUsual P) (hD : MemLp D 2 P) (hW : MemLp W 2 P)
    (hm : ∀ i, StronglyMeasurable[F (e i)] (C i)) (hi : ∀ i, Integrable (C i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖P[D - C i | F (e i)] ω‖ ≤ P[W | F (e i)] ω) :
    let S : Ω → ℝ≥0∞ := fun ω ↦ ⨆ i, ENNReal.ofReal ‖C i ω‖
    Measurable S ∧ (∀ᵐ ω ∂P, S ω ≠ ∞) ∧ MemLp (fun ω ↦ (S ω).toReal) 2 P ∧
      (∫ ω, (S ω).toReal ^ 2 ∂P) ≤
        8 * ((∫ ω, D ω ^ 2 ∂P) + ∫ ω, W ω ^ 2 ∂P) := by
  intro S
  obtain ⟨g, _, hgn, hgL, hgb, hgE⟩ :=
    exists_memLp_two_countable_condExp_tail_envelope hF hD hW hm hi hb
  have hSm : Measurable S := Measurable.iSup fun i ↦
    ENNReal.measurable_ofReal.comp (((hm i).mono (F.le (e i))).measurable.norm)
  have hSg : ∀ᵐ ω ∂P, S ω ≤ ENNReal.ofReal (g ω) := by
    filter_upwards [hgb] with ω hω
    exact iSup_le fun i ↦ ENNReal.ofReal_le_ofReal (hω i)
  have hSf : ∀ᵐ ω ∂P, S ω ≠ ∞ :=
    hSg.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hrg : ∀ᵐ ω ∂P, (S ω).toReal ≤ g ω := by
    filter_upwards [hSg] with ω hω
    simpa only [ENNReal.toReal_ofReal (hgn ω)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  have hSL : MemLp (fun ω ↦ (S ω).toReal) 2 P := by
    apply hgL.mono hSm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hrg] with ω hω
    simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (hgn ω)]
      using hω
  refine ⟨hSm, hSf, hSL, le_trans ?_ hgE⟩
  apply integral_mono_ae hSL.integrable_sq hgL.integrable_sq
  filter_upwards [hrg] with ω hω
  exact (sq_le_sq₀ ENNReal.toReal_nonneg (hgn ω)).mpr hω

/-- A probability bound for an actual exceedance at any observation time. -/
theorem measureReal_exists_norm_gt_le_of_condExp_tail_bound
    (hF : F.IsUsual P) (hD : MemLp D 2 P) (hW : MemLp W 2 P)
    (hm : ∀ i, StronglyMeasurable[F (e i)] (C i)) (hi : ∀ i, Integrable (C i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖P[D - C i | F (e i)] ω‖ ≤ P[W | F (e i)] ω)
    {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ i, a < ‖C i ω‖} ≤
      8 * ((∫ ω, D ω ^ 2 ∂P) + ∫ ω, W ω ^ 2 ∂P) / a ^ 2 := by
  obtain ⟨g, _, _, hgL, hgb, hgE⟩ :=
    exists_memLp_two_countable_condExp_tail_envelope hF hD hW hm hi hb
  have hsub : P {ω | ∃ i, a < ‖C i ω‖} ≤ P {ω | a ≤ ‖g ω‖} := by
    apply measure_mono_ae
    filter_upwards [hgb] with ω hω hiω
    obtain ⟨i, hi⟩ := hiω
    exact (hi.le.trans (hω i)).trans (le_abs_self _)
  have hbound := measure_norm_ge_le_integral_sq_div hgL.integrable_sq ha
  have hreal : P.real {ω | a ≤ ‖g ω‖} ≤ (∫ ω, g ω ^ 2 ∂P) / a ^ 2 := by
    rw [Measure.real]
    simpa only [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun ω ↦ sq_nonneg _)
      (sq_nonneg a))] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (hreal.trans (div_le_div_of_nonneg_right hgE (sq_nonneg a)))

/-- A genuine countable value representation transfers the envelope to the whole
compact interval. A dyadic caller must prove this from the step-cell formulas;
left continuity alone does not determine the values between fixed grid points. -/
theorem exists_memLp_two_compact_envelope_of_countable_condExp_tail_bound
    {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hF : F.IsUsual P) (hD : MemLp D 2 P) (hW : MemLp W 2 P)
    (hm : ∀ i, StronglyMeasurable[F (e i)] (C i)) (hi : ∀ i, Integrable (C i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖P[D - C i | F (e i)] ω‖ ≤ P[W | F (e i)] ω)
    (hcover : ∀ᵐ ω ∂P, ∀ t ≤ T, ∃ i, Y t ω = C i ω) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, ‖Y t ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 8 * ((∫ ω, D ω ^ 2 ∂P) + ∫ ω, W ω ^ 2 ∂P) := by
  obtain ⟨g, hgm, hgn, hgL, hgb, hgE⟩ :=
    exists_memLp_two_countable_condExp_tail_envelope hF hD hW hm hi hb
  refine ⟨g, hgm, hgn, hgL, ?_, hgE⟩
  filter_upwards [hgb, hcover] with ω hbω hcω t ht
  obtain ⟨i, hi⟩ := hcω t ht
  simpa only [hi] using hbω i

theorem measureReal_exists_time_norm_gt_le_of_countable_condExp_tail_bound
    {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hF : F.IsUsual P) (hD : MemLp D 2 P) (hW : MemLp W 2 P)
    (hm : ∀ i, StronglyMeasurable[F (e i)] (C i)) (hi : ∀ i, Integrable (C i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖P[D - C i | F (e i)] ω‖ ≤ P[W | F (e i)] ω)
    (hcover : ∀ᵐ ω ∂P, ∀ t ≤ T, ∃ i, Y t ω = C i ω) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ t ≤ T, a < ‖Y t ω‖} ≤
      8 * ((∫ ω, D ω ^ 2 ∂P) + ∫ ω, W ω ^ 2 ∂P) / a ^ 2 := by
  have hsub : P {ω | ∃ t ≤ T, a < ‖Y t ω‖} ≤ P {ω | ∃ i, a < ‖C i ω‖} := by
    apply measure_mono_ae
    filter_upwards [hcover] with ω hcω hω
    obtain ⟨t, ht, hta⟩ := hω
    obtain ⟨i, hi⟩ := hcω t ht
    exact ⟨i, by simpa only [hi] using hta⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (measureReal_exists_norm_gt_le_of_condExp_tail_bound hF hD hW hm hi hb ha)

end MeasureTheory
