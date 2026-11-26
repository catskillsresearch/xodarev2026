/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.NflvrBoundedBelow
public import SignatureVolatility.NflvrContIto

@[expose] public section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Section 1: Elementary Bridges & `L²` Helpers -/

private def sigFiltrationM {d : ℕ} (B : MultiBrownian Ω P d) : ℝ → MeasurableSpace Ω :=
  (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
    (measurable_paperSig2_coeff B 0)).σAlg

private def elemPredToJoint {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ}
    (U : ElemPredProcess (sigFiltrationM B) T) : JointElem B T where
  n := U.n
  a := U.a
  b := U.b
  h := U.h
  hab := U.hab
  h_meas := fun j => by
    have hm := U.h_meas j
    have hEq : sigFiltrationM B (U.a j) = (pathFiltration B).σAlg (U.a j) :=
      sigFiltration_eq_pathFiltration B (U.a j)
    rwa [hEq] at hm
  h_bdd := U.h_bdd

private def jointToElemPred {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ}
    (U : JointElem B T) : ElemPredProcess (sigFiltrationM B) T where
  n := U.n
  a := U.a
  b := U.b
  h := U.h
  hab := U.hab
  h_meas := fun j => by
    have hm := U.h_meas j
    have hEq : sigFiltrationM B (U.a j) = (pathFiltration B).σAlg (U.a j) :=
      sigFiltration_eq_pathFiltration B (U.a j)
    rwa [← hEq] at hm
  h_bdd := U.h_bdd

private lemma jointElem_ito_meas' {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (U : JointElem B T) {t : ℝ} (ht0 : 0 ≤ t) :
    Measurable[(pathFiltration B).σAlg t] (U.ito hd t) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases hle : U.a j ≤ t
  · have hb0 : 0 ≤ min (U.b j) t := le_min ((U.hab j).1.trans (U.hab j).2.1) ht0
    have ha0 : 0 ≤ min (U.a j) t := le_min (U.hab j).1 ht0
    exact ((U.h_meas j).mono ((pathFiltration B).mono hle) le_rfl).mul
      ((measurable_W_pathFiltration B ⟨min (U.b j) t, hb0, min_le_right _ _⟩ (kitDriver hd)).sub
       (measurable_W_pathFiltration B ⟨min (U.a j) t, ha0, min_le_right _ _⟩ (kitDriver hd)))
  · have hlt : t ≤ U.a j := le_of_not_ge hle
    have h0 : (fun ω => U.h j ω * (MultiBrownian.W B (min (U.b j) t) ω (kitDriver hd) -
        MultiBrownian.W B (min (U.a j) t) ω (kitDriver hd))) = fun _ => 0 := funext fun ω => by
      rw [min_eq_right (hlt.trans (U.hab j).2.1), min_eq_right hlt, sub_self, mul_zero]
    rw [h0]; exact measurable_const

private lemma jointElem_ito_memLp' {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (U : JointElem B T) {t : ℝ} (ht0 : 0 ≤ t) :
    MemLp (U.ito hd t) 2 P := by
  have hrew : U.ito hd t = fun ω => ∑ j : Fin U.n,
      U.h j ω * wnnIncr B (kitDriver hd) (min (U.a j) t) (min (U.b j) t) ω :=
    funext fun ω => Finset.sum_congr rfl fun j _ => by simp only [wnnIncr_eq_W]
  rw [hrew]
  refine memLp_finsetSum Finset.univ fun j _ => ?_
  obtain ⟨C, hC⟩ := U.h_bdd j
  have hW := (hasLaw_wnnIncr B (kitDriver hd) (le_min (U.hab j).1 ht0)
    (min_le_min_right t (U.hab j).2.1)).memLp (memLp_id_gaussianReal' 2 (by simp))
  refine (hW.abs.const_mul (max C 0)).mono
    (((U.h_meas j).mono ((pathFiltration B).le_ambient _) le_rfl).mul
      (measurable_wnnIncr B (kitDriver hd) _ _)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Pi.abs_apply, abs_abs, abs_of_nonneg (le_max_right C 0)]
  exact mul_le_mul_of_nonneg_right ((hC ω).trans (le_max_left C 0)) (abs_nonneg _)

private lemma integral_jointElem_ito_zero {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d)
    {T : ℝ} (hT : 0 ≤ T) (U : JointElem B T) :
    ∫ ω, U.ito hd T ω ∂P = 0 := by
  have h := setIntegral_jointElem_ito hd U le_rfl hT le_rfl MeasurableSet.univ
  have h0 : U.ito hd 0 = fun _ => 0 := funext fun ω => Finset.sum_eq_zero fun j _ => by
    rw [min_eq_right (U.hab j).1, min_eq_right ((U.hab j).1.trans (U.hab j).2.1), sub_self, mul_zero]
  simpa [h0] using h

private lemma l2_abs_integral_le_sqrt {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  set a := Real.sqrt (∫ ω, f ω ^ 2 ∂P)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ∫ ω, f ω ^ 2 ∂P := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  by_cases ha : a = 0
  · have h0 : ∫ ω, f ω ^ 2 ∂P = 0 := by rw [← ha2, ha]; ring
    have hf0 : f =ᵐ[P] 0 :=
      ((integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hf.integrable_sq).mp h0).mono
        fun ω hω => sq_eq_zero_iff.mp hω
    have habs0 : (fun ω => |f ω|) =ᵐ[P] fun _ => (0 : ℝ) :=
      hf0.mono fun ω hω => by simp only [Pi.zero_apply] at hω; simp [hω]
    rw [ha, integral_congr_ae habs0, integral_zero]
  · have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hpt : ∀ ω, |f ω| ≤ f ω ^ 2 / (2 * a) + a / 2 := fun ω => by
      have hsq := sq_nonneg (|f ω| - a)
      have h2 : 2 * a * |f ω| ≤ f ω ^ 2 + a ^ 2 := by nlinarith [sq_abs (f ω)]
      have h2a : 0 < 2 * a := by positivity
      have hdiv := (div_le_div_iff_of_pos_right h2a).mpr h2
      have hL : 2 * a * |f ω| / (2 * a) = |f ω| := mul_div_cancel_left₀ _ h2a.ne'
      have hR : (f ω ^ 2 + a ^ 2) / (2 * a) = f ω ^ 2 / (2 * a) + a / 2 := by field_simp [hap.ne']
      rwa [hL, hR] at hdiv
    calc ∫ ω, |f ω| ∂P
        ≤ ∫ ω, (f ω ^ 2 / (2 * a) + a / 2) ∂P :=
          integral_mono (hf.integrable one_le_two).abs
            ((hf.integrable_sq.div_const (2 * a)).add (integrable_const (a / 2))) hpt
      _ = a ^ 2 / (2 * a) + a / 2 := by
          rw [integral_add (hf.integrable_sq.div_const _) (integrable_const _),
            integral_div, integral_const, probReal_univ, one_smul, ha2]
      _ = a := by field_simp [hap.ne']; ring

private lemma enorm_rpow_two (x : ℝ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two, sq_abs]

/-! ## Section 2: Mean Zero & Delbaen–Schachermayer NFLVR for Genuine `L²` Itô Gains -/

/-- Every genuine `L²` Itô integral `V` against the first coordinate of `B` on the full
signature filtration `(sigFiltration B).σAlg` (any `d ≥ 1`, no H3) has `V T ∈ L²(P)` with
`∫ ω, V T ω ∂P = 0`. -/
theorem expectation_eq_zero_of_isL2ItoIntegral {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T) {K V : ℝ → Ω → ℝ}
    (hIto : IsL2ItoIntegral P (sigFiltrationM B)
      (fun t ω => MultiBrownian.W B t ω (kitDriver hd)) K V T) :
    Integrable (V T) P ∧ ∫ ω, V T ω ∂P = 0 := by
  obtain ⟨-, -, hV_aesm, -, U, -, hU_V⟩ := hIto
  let UJ : ℕ → JointElem B T := fun m => elemPredToJoint B (U m)
  have hlim := hU_V T ⟨hT.le, le_rfl⟩
  have hVT_aesm : AEStronglyMeasurable (V T) P := hV_aesm T ⟨hT.le, le_rfl⟩
  obtain ⟨m₀, hm₀⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) 1 zero_lt_one
  have hm₀_lt : ∫⁻ ω, ENNReal.ofReal (((UJ m₀).ito hd T ω - V T ω) ^ 2) ∂P < ⊤ :=
    (hm₀ m₀ le_rfl).trans_lt ENNReal.one_lt_top
  have hdiff_aesm : AEStronglyMeasurable (fun ω => (UJ m₀).ito hd T ω - V T ω) P :=
    ((jointElem_ito_meas' hd (UJ m₀) hT.le).mono ((pathFiltration B).le_ambient T) le_rfl).aestronglyMeasurable.sub
      hVT_aesm
  have hdiff_L2 : MemLp (fun ω => (UJ m₀).ito hd T ω - V T ω) 2 P := by
    change eLpNorm (fun ω => (UJ m₀).ito hd T ω - V T ω) 2 P < ∞
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hdiff_aesm]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [enorm_rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hm₀_lt.ne
  have hVT_L2 : MemLp (V T) 2 P := by
    have hsub := (jointElem_ito_memLp' hd (UJ m₀) hT.le).sub hdiff_L2
    have heq : (UJ m₀).ito hd T - (fun ω => (UJ m₀).ito hd T ω - V T ω) = V T :=
      funext fun ω => sub_sub_cancel _ _
    rwa [heq] at hsub
  have hVT_int : Integrable (V T) P := hVT_L2.integrable one_le_two
  refine ⟨hVT_int, eq_of_forall_dist_le fun ε hε => ?_⟩
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) (ENNReal.ofReal (ε ^ 2))
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε))
  have hm_le : ∫⁻ ω, ENNReal.ofReal (((UJ m).ito hd T ω - V T ω) ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2) :=
    hm m le_rfl
  have hi_sq : Integrable (fun ω => ((UJ m).ito hd T ω - V T ω) ^ 2) P :=
    ((jointElem_ito_memLp' hd (UJ m) hT.le).sub hVT_L2).integrable_sq
  have hsq_le : ∫ ω, ((UJ m).ito hd T ω - V T ω) ^ 2 ∂P ≤ ε ^ 2 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg ε),
      ofReal_integral_eq_lintegral_ofReal hi_sq (ae_of_all _ fun _ => sq_nonneg _)]
    exact hm_le
  have hsub_int : ∫ ω, ((UJ m).ito hd T ω - V T ω) ∂P = -(∫ ω, V T ω ∂P) := by
    rw [integral_sub ((jointElem_ito_memLp' hd (UJ m) hT.le).integrable one_le_two) hVT_int,
      integral_jointElem_ito_zero hd hT.le (UJ m), zero_sub]
  rw [Real.dist_eq, sub_zero, ← abs_neg, ← hsub_int]
  calc |∫ ω, ((UJ m).ito hd T ω - V T ω) ∂P|
      ≤ ∫ ω, |(UJ m).ito hd T ω - V T ω| ∂P := abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ ω, ((UJ m).ito hd T ω - V T ω) ^ 2 ∂P) :=
        l2_abs_integral_le_sqrt ((jointElem_ito_memLp' hd (UJ m) hT.le).sub hVT_L2)
    _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = ε := Real.sqrt_sq hε.le

/-- **Delbaen–Schachermayer NFLVR for genuine `L²` Itô bounded-below gains** (any `d ≥ 1`,
any `S` and `σ`, no H3). -/
theorem satisfiesNFLVR_DS_boundedBelowGains_any {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T) (S σ : ℝ → Ω → ℝ) :
    SatisfiesNFLVR_DS P
      (BoundedBelowGains
        (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
          (measurable_paperSig2_coeff B 0)).σAlg P
        (fun t ω => MultiBrownian.W B t ω (kitDriver hd)) S σ T) := by
  refine nflvr_ds_of_nonpos_mean ?_
  rintro _ ⟨H, V, a, -, -, hIto, rfl⟩
  obtain ⟨hInt, hEq0⟩ := expectation_eq_zero_of_isL2ItoIntegral hd B hT hIto
  exact ⟨hInt, hEq0.le⟩

end SignatureVolatility
