/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.NflvrBoundedBelow

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Section 0: Carathéodory Joint Measurability Helper -/

/-- If `t ↦ F t ω` is continuous for every `ω` and `ω ↦ F t ω` is measurable for every `t`,
then `(t, ω) ↦ F t ω` is jointly measurable. -/
private lemma measurable_uncurry_of_continuous_left {F : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous (fun t => F t ω))
    (hmeas : ∀ t : ℝ, Measurable (F t)) :
    Measurable (fun p : ℝ × Ω => F p.1 p.2) := by
  let approx (r : ℕ) (p : ℝ × Ω) : ℝ :=
    F ((⌊p.1 * (2 ^ r : ℝ)⌋ : ℝ) / (2 ^ r : ℝ)) p.2
  have happrox_m : ∀ r : ℕ, Measurable (approx r) := fun r => by
    intro S hS
    have heq : approx r ⁻¹' S =
        ⋃ k : ℤ, ({t : ℝ | ⌊t * (2 ^ r : ℝ)⌋ = k} ×ˢ (F ((k : ℝ) / (2 ^ r : ℝ)) ⁻¹' S)) := by
      ext ⟨t, ω⟩
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, approx]
      constructor
      · intro h; exact ⟨⌊t * (2 ^ r : ℝ)⌋, rfl, h⟩
      · rintro ⟨k, rfl, h⟩; exact h
    rw [heq]
    refine MeasurableSet.iUnion fun k => ?_
    have hfloor : {t : ℝ | ⌊t * (2 ^ r : ℝ)⌋ = k} =
        Ico ((k : ℝ) / (2 ^ r : ℝ)) (((k : ℝ) + 1) / (2 ^ r : ℝ)) := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_Ico, Int.floor_eq_iff]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
      rw [div_le_iff₀ hpos, lt_div_iff₀ hpos]
    rw [hfloor]
    exact measurableSet_Ico.prod (hmeas _ hS)
  have hlim : ∀ p : ℝ × Ω, Tendsto (fun r => approx r p) atTop (𝓝 (F p.1 p.2)) := fun ⟨t, ω⟩ => by
    have hpt : Tendsto (fun r : ℕ => ((⌊t * (2 ^ r : ℝ)⌋ : ℝ) / (2 ^ r : ℝ))) atTop (𝓝 t) := by
      have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / (2 ^ r : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using tendsto_const_nhds.sub h0)
        tendsto_const_nhds (fun r => ?_) (fun r => ?_)
      · have hpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
        have hle : t * (2 ^ r : ℝ) - 1 ≤ (⌊t * (2 ^ r : ℝ)⌋ : ℝ) := (Int.sub_one_lt_floor _).le
        have hdiv := (div_le_div_iff_of_pos_right hpos).mpr hle
        rw [sub_div, mul_div_cancel_right₀ _ hpos.ne'] at hdiv
        rw [inv_eq_one_div]
        exact hdiv
      · have hpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
        rw [div_le_iff₀ hpos]; exact Int.floor_le (t * (2 ^ r : ℝ))
    exact ((hcont ω).tendsto t).comp hpt
  exact measurable_of_tendsto_metrizable happrox_m (tendsto_pi_nhds.mpr hlim)

private lemma measurable_eval_prod {γ : Type*} [MeasurableSpace γ] (f : ℝ × Ω → γ)
    (hf : Measurable f) (t : ℝ) : Measurable (fun ω : Ω => f (t, ω)) :=
  hf.comp (measurable_const.prodMk measurable_id)

/-! ## Section 1: Self-Contained Cauchy–Schwarz & Discrete Doob L² Maximal Inequality -/

private lemma integral_mul_le_sqrt_mul_sqrt {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, |f ω| * |g ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  set a := Real.sqrt (∫ ω, f ω ^ 2 ∂P)
  set b := Real.sqrt (∫ ω, g ω ^ 2 ∂P)
  have ha2 : a ^ 2 = ∫ ω, f ω ^ 2 ∂P := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hb2 : b ^ 2 = ∫ ω, g ω ^ 2 ∂P := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  by_cases ha : a = 0
  · have hf0 : f =ᵐ[P] 0 := by
      have h0 : ∫ ω, f ω ^ 2 ∂P = 0 := by rw [← ha2, ha]; ring
      exact ((integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hf.integrable_sq).mp h0).mono
        fun ω hω => sq_eq_zero_iff.mp hω
    have hzero : (fun ω => |f ω| * |g ω|) =ᵐ[P] fun _ => (0 : ℝ) :=
      hf0.mono fun ω hω => by simp only [Pi.zero_apply] at hω; simp [hω]
    rw [ha, zero_mul, integral_congr_ae hzero, integral_zero]
  · have hap : 0 < a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
    by_cases hb : b = 0
    · have hg0 : g =ᵐ[P] 0 := by
        have h0 : ∫ ω, g ω ^ 2 ∂P = 0 := by rw [← hb2, hb]; ring
        exact ((integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hg.integrable_sq).mp h0).mono
          fun ω hω => sq_eq_zero_iff.mp hω
      have hzero : (fun ω => |f ω| * |g ω|) =ᵐ[P] fun _ => (0 : ℝ) :=
        hg0.mono fun ω hω => by simp only [Pi.zero_apply] at hω; simp [hω]
      rw [hb, mul_zero, integral_congr_ae hzero, integral_zero]
    · have hbp : 0 < b := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb)
      have hpt : ∀ ω, |f ω| * |g ω| ≤ (b / (2 * a)) * f ω ^ 2 + (a / (2 * b)) * g ω ^ 2 := fun ω => by
        have hsq := sq_nonneg (b * |f ω| - a * |g ω|)
        have h2 : 2 * a * b * (|f ω| * |g ω|) ≤ b ^ 2 * f ω ^ 2 + a ^ 2 * g ω ^ 2 := by
          nlinarith [sq_abs (f ω), sq_abs (g ω)]
        have hab : 0 < 2 * a * b := by positivity
        have hdiv := (div_le_div_iff_of_pos_right hab).mpr h2
        have hL : 2 * a * b * (|f ω| * |g ω|) / (2 * a * b) = |f ω| * |g ω| :=
          mul_div_cancel_left₀ _ hab.ne'
        have hR : (b ^ 2 * f ω ^ 2 + a ^ 2 * g ω ^ 2) / (2 * a * b) =
            (b / (2 * a)) * f ω ^ 2 + (a / (2 * b)) * g ω ^ 2 := by
          field_simp [hap.ne', hbp.ne']
        rwa [hL, hR] at hdiv
      have hi := integrable_mul_of_memLp_two hf.abs hg.abs
      calc ∫ ω, |f ω| * |g ω| ∂P
          ≤ ∫ ω, ((b / (2 * a)) * f ω ^ 2 + (a / (2 * b)) * g ω ^ 2) ∂P :=
            integral_mono hi ((hf.integrable_sq.const_mul _).add (hg.integrable_sq.const_mul _)) hpt
        _ = (b / (2 * a)) * a ^ 2 + (a / (2 * b)) * b ^ 2 := by
            rw [integral_add (hf.integrable_sq.const_mul _) (hg.integrable_sq.const_mul _),
              integral_const_mul, integral_const_mul, ha2, hb2]
        _ = a * b := by field_simp [hap.ne', hbp.ne']; ring

private lemma integral_abs_le_sqrt_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have h := integral_mul_le_sqrt_mul_sqrt hf (memLp_const (1 : ℝ))
  simp only [abs_one, mul_one, one_pow, integral_const, probReal_univ, one_smul, Real.sqrt_one] at h
  exact h

/-- **Discrete Doob L² maximal inequality** proved directly from scratch:
if `M 0, …, M N ∈ L²` is a martingale on `𝒢 0 ≤ … ≤ 𝒢 N`, then
`𝔼[(max_{k ≤ N} |M k|)²] ≤ 4 𝔼[(M N)²]`. -/
lemma doob_l2_maximal_discrete {N : ℕ} (𝒢 : Fin (N + 1) → MeasurableSpace Ω)
    (h𝒢_mono : Monotone 𝒢) (h𝒢_le : ∀ k, 𝒢 k ≤ m₀)
    (M : Fin (N + 1) → Ω → ℝ)
    (hM_meas : ∀ k, Measurable[𝒢 k] (M k))
    (hM_L2 : ∀ k, MemLp (M k) 2 P)
    (hM_mart : ∀ (k : Fin (N + 1)) (A : Set Ω), MeasurableSet[𝒢 k] A →
      ∫ ω in A, M (Fin.last N) ω ∂P = ∫ ω in A, M k ω ∂P) :
    let Mstar : Ω → ℝ := fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (fun k => |M k ω|)
    Integrable (fun ω => Mstar ω ^ 2) P ∧
      ∫ ω, Mstar ω ^ 2 ∂P ≤ 4 * ∫ ω, M (Fin.last N) ω ^ 2 ∂P := by
  intro Mstar
  have hM_amb : ∀ k, Measurable (M k) := fun k => (hM_meas k).mono (h𝒢_le k) le_rfl
  have hMstar_nn : ∀ ω, 0 ≤ Mstar ω := fun ω =>
    le_trans (abs_nonneg (M 0 ω)) (Finset.le_sup' (fun k => |M k ω|) (Finset.mem_univ 0))
  have hMstar_le_sum : ∀ ω, Mstar ω ≤ ∑ k : Fin (N + 1), |M k ω| := fun ω =>
    Finset.sup'_le _ _ fun k _ => Finset.single_le_sum (fun j _ => abs_nonneg (M j ω)) (Finset.mem_univ k)
  have hMstar_meas : Measurable Mstar := measurable_of_Iic fun c => by
    have heq : Mstar ⁻¹' Iic c = ⋂ k : Fin (N + 1), {ω | |M k ω| ≤ c} := by
      ext ω; simp [Mstar, Finset.sup'_le_iff]
    rw [heq]; exact MeasurableSet.iInter fun k => measurableSet_le (hM_amb k).abs measurable_const
  have hMstar_L2 : MemLp Mstar 2 P := by
    have hsum_L2 : MemLp (fun ω => ∑ k : Fin (N + 1), |M k ω|) 2 P :=
      memLp_finsetSum Finset.univ fun k _ => (hM_L2 k).abs
    refine hsum_L2.mono hMstar_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (hMstar_nn ω), Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    exact hMstar_le_sum ω
  refine ⟨hMstar_L2.integrable_sq, ?_⟩
  have hsub : ∀ (k : Fin (N + 1)) (A : Set Ω), MeasurableSet[𝒢 k] A →
      ∫ ω in A, |M k ω| ∂P ≤ ∫ ω in A, |M (Fin.last N) ω| ∂P := by
    intro k A hA
    set Ap : Set Ω := A ∩ {ω | 0 ≤ M k ω}
    set Am : Set Ω := A ∩ {ω | M k ω < 0}
    have hAp : MeasurableSet[𝒢 k] Ap := by
      have hm := hM_meas k
      let : MeasurableSpace Ω := 𝒢 k
      exact hA.inter (measurableSet_le measurable_const hm)
    have hAm : MeasurableSet[𝒢 k] Am := by
      have hm := hM_meas k
      let : MeasurableSpace Ω := 𝒢 k
      exact hA.inter (measurableSet_lt hm measurable_const)
    have hdisj : Disjoint Ap Am := Set.disjoint_left.mpr fun ω h1 h2 =>
      not_lt.mpr (show 0 ≤ M k ω from h1.2) (show M k ω < 0 from h2.2)
    have hunion : A = Ap ∪ Am := by
      ext ω; simp only [Ap, Am, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h; rcases le_or_gt 0 (M k ω) with h0 | h0; exact Or.inl ⟨h, h0⟩; exact Or.inr ⟨h, h0⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hi_k := (hM_L2 k).integrable one_le_two
    have hi_N := (hM_L2 (Fin.last N)).integrable one_le_two
    have hp : ∫ ω in Ap, |M k ω| ∂P ≤ ∫ ω in Ap, |M (Fin.last N) ω| ∂P := by
      calc ∫ ω in Ap, |M k ω| ∂P = ∫ ω in Ap, M k ω ∂P :=
            setIntegral_congr_fun (h𝒢_le k _ hAp) fun ω hω => abs_of_nonneg hω.2
        _ = ∫ ω in Ap, M (Fin.last N) ω ∂P := (hM_mart k Ap hAp).symm
        _ ≤ ∫ ω in Ap, |M (Fin.last N) ω| ∂P :=
            setIntegral_mono_on hi_N.integrableOn hi_N.abs.integrableOn (h𝒢_le k _ hAp) fun ω _ => le_abs_self _
    have hm : ∫ ω in Am, |M k ω| ∂P ≤ ∫ ω in Am, |M (Fin.last N) ω| ∂P := by
      calc ∫ ω in Am, |M k ω| ∂P = -(∫ ω in Am, M k ω ∂P) := by
            rw [← integral_neg]; exact setIntegral_congr_fun (h𝒢_le k _ hAm) fun ω hω => abs_of_neg hω.2
        _ = -(∫ ω in Am, M (Fin.last N) ω ∂P) := by rw [hM_mart k Am hAm]
        _ = ∫ ω in Am, (-M (Fin.last N) ω) ∂P := (integral_neg _).symm
        _ ≤ ∫ ω in Am, |M (Fin.last N) ω| ∂P :=
            setIntegral_mono_on hi_N.neg.integrableOn hi_N.abs.integrableOn (h𝒢_le k _ hAm) fun ω _ => neg_le_abs _
    rw [hunion, setIntegral_union hdisj (h𝒢_le k _ hAm) hi_k.abs.integrableOn hi_k.abs.integrableOn,
      setIntegral_union hdisj (h𝒢_le k _ hAm) hi_N.abs.integrableOn hi_N.abs.integrableOn]
    exact add_le_add hp hm
  have hweak : ∀ lam : ℝ, 0 < lam →
      ENNReal.ofReal lam * P {ω | lam ≤ Mstar ω} ≤
        ∫⁻ ω in {ω | lam ≤ Mstar ω}, ENNReal.ofReal |M (Fin.last N) ω| ∂P := by
    intro lam _
    let A : Fin (N + 1) → Set Ω := fun k =>
      {ω | lam ≤ |M k ω|} ∩ ⋂ (j : Fin (N + 1)) (_ : j < k), {ω | |M j ω| < lam}
    have hA_meas : ∀ k, MeasurableSet[𝒢 k] (A k) := fun k => by
      have hm_k : MeasurableSet[𝒢 k] {ω | lam ≤ |M k ω|} := by
        have hmk := hM_meas k
        let : MeasurableSpace Ω := 𝒢 k
        exact measurableSet_le measurable_const hmk.abs
      have hm_lt : ∀ j : Fin (N + 1), j < k → MeasurableSet[𝒢 k] {ω | |M j ω| < lam} := fun j hjk => by
        have hmj : MeasurableSet[𝒢 j] {ω | |M j ω| < lam} := by
          have hm := hM_meas j
          let : MeasurableSpace Ω := 𝒢 j
          exact measurableSet_lt hm.abs measurable_const
        exact h𝒢_mono hjk.le _ hmj
      let : MeasurableSpace Ω := 𝒢 k
      exact hm_k.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun hjk => hm_lt j hjk)
    have hA_amb : ∀ k, MeasurableSet (A k) := fun k => h𝒢_le k _ (hA_meas k)
    have hA_disj : Pairwise fun i j : Fin (N + 1) => Disjoint (A i) (A j) := fun i j hij =>
      Set.disjoint_left.mpr fun ω hi hj => by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have hi1 : lam ≤ |M i ω| := hi.1
          have hj_lt : |M i ω| < lam := Set.mem_iInter.mp (Set.mem_iInter.mp hj.2 i) hlt
          exact not_le.mpr hj_lt hi1
        · have hj1 : lam ≤ |M j ω| := hj.1
          have hi_lt : |M j ω| < lam := Set.mem_iInter.mp (Set.mem_iInter.mp hi.2 j) hgt
          exact not_le.mpr hi_lt hj1
    have hA_union : {ω | lam ≤ Mstar ω} = ⋃ k : Fin (N + 1), A k := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, A, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro h
        have hex : ∃ k : Fin (N + 1), lam ≤ |M k ω| := by
          obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => |M k ω|)
          exact ⟨k, hk ▸ h⟩
        let F := Finset.univ.filter fun k : Fin (N + 1) => lam ≤ |M k ω|
        have hF : F.Nonempty := by obtain ⟨k, hk⟩ := hex; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
        let k0 := F.min' hF
        refine ⟨k0, (Finset.mem_filter.mp (F.min'_mem hF)).2, fun j hjk => ?_⟩
        by_contra hge; push Not at hge
        exact not_le.mpr hjk (F.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hge⟩))
      · rintro ⟨k, hk, _⟩; exact hk.trans (Finset.le_sup' (fun j => |M j ω|) (Finset.mem_univ k))
    have hstep_k : ∀ k, ENNReal.ofReal lam * P (A k) ≤
        ∫⁻ ω in A k, ENNReal.ofReal |M (Fin.last N) ω| ∂P := fun k => by
      have hi_k := ((hM_L2 k).integrable one_le_two).abs.integrableOn (s := A k)
      have hi_N := ((hM_L2 (Fin.last N)).integrable one_le_two).abs.integrableOn (s := A k)
      calc ENNReal.ofReal lam * P (A k)
          = ∫⁻ _ω in A k, ENNReal.ofReal lam ∂P := (setLIntegral_const (A k) _).symm
        _ ≤ ∫⁻ ω in A k, ENNReal.ofReal |M k ω| ∂P :=
            lintegral_mono_ae (ae_restrict_of_forall_mem (hA_amb k) fun ω hω => ENNReal.ofReal_le_ofReal hω.1)
        _ = ENNReal.ofReal (∫ ω in A k, |M k ω| ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal hi_k (ae_of_all _ fun _ => abs_nonneg _)).symm
        _ ≤ ENNReal.ofReal (∫ ω in A k, |M (Fin.last N) ω| ∂P) :=
            ENNReal.ofReal_le_ofReal (hsub k (A k) (hA_meas k))
        _ = ∫⁻ ω in A k, ENNReal.ofReal |M (Fin.last N) ω| ∂P :=
            ofReal_integral_eq_lintegral_ofReal hi_N (ae_of_all _ fun _ => abs_nonneg _)
    rw [hA_union, measure_iUnion hA_disj hA_amb, ← ENNReal.tsum_mul_left, lintegral_iUnion hA_amb hA_disj]
    exact ENNReal.tsum_le_tsum hstep_k
  -- Layer-cake: `𝔼[Mstar²] = ∫₀^∞ 2 λ P(Mstar ≥ λ) dλ ≤ 2 𝔼[|M N| * Mstar]`
  have hlayer_L : ∫⁻ ω, ENNReal.ofReal (Mstar ω ^ 2) ∂P =
      ∫⁻ lam in Ioi (0 : ℝ), ENNReal.ofReal (2 * lam) * P {ω | lam ≤ Mstar ω} ∂volume := by
    have hpt : ∀ ω, ENNReal.ofReal (Mstar ω ^ 2) =
        ∫⁻ lam in Ioi (0 : ℝ), {p : Ω × ℝ | p.2 ≤ Mstar p.1}.indicator
          (fun p => ENNReal.ofReal (2 * p.2)) (ω, lam) ∂volume := fun ω => by
      have heq : ∫⁻ lam in Ioi (0 : ℝ), {p : Ω × ℝ | p.2 ≤ Mstar p.1}.indicator
            (fun p => ENNReal.ofReal (2 * p.2)) (ω, lam) ∂volume =
          ∫⁻ lam in Ioc 0 (Mstar ω), ENNReal.ofReal (2 * lam) ∂volume := by
        rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
        congr 1; funext lam
        by_cases h1 : 0 < lam <;> by_cases h2 : lam ≤ Mstar ω <;> simp [Set.indicator, h1, h2]
      rw [heq]
      have hint : IntegrableOn (fun lam : ℝ => 2 * lam) (Ioc 0 (Mstar ω)) volume :=
        (continuous_const.mul continuous_id).integrableOn_Ioc
      rw [← ofReal_integral_eq_lintegral_ofReal hint
          (ae_restrict_of_forall_mem measurableSet_Ioc fun lam hl => show (0 : ℝ) ≤ 2 * lam by linarith [hl.1]),
        ← intervalIntegral.integral_of_le (hMstar_nn ω), intervalIntegral.integral_const_mul,
        integral_id, zero_pow two_ne_zero, sub_zero]
      congr 1; ring
    simp_rw [hpt]
    have hmeas_ind : Measurable (fun p : Ω × ℝ =>
        {q : Ω × ℝ | q.2 ≤ Mstar q.1}.indicator (fun q => ENNReal.ofReal (2 * q.2)) p) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_snd)).indicator
        (measurableSet_le measurable_snd (hMstar_meas.comp measurable_fst))
    rw [lintegral_lintegral_swap hmeas_ind.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun lam _ => ?_
    rw [← setLIntegral_const {ω | lam ≤ Mstar ω} (ENNReal.ofReal (2 * lam)),
      ← lintegral_indicator (measurableSet_le measurable_const hMstar_meas)]
    refine congrArg _ (funext fun ω => ?_)
    by_cases h : lam ≤ Mstar ω <;> simp [Set.indicator, h]
  have hlayer_R : ∫⁻ lam in Ioi (0 : ℝ),
        (2 : ℝ≥0∞) * ∫⁻ ω in {ω | lam ≤ Mstar ω}, ENNReal.ofReal |M (Fin.last N) ω| ∂P ∂volume =
      ∫⁻ ω, ENNReal.ofReal (2 * |M (Fin.last N) ω| * Mstar ω) ∂P := by
    have hrew : ∀ lam : ℝ,
        (2 : ℝ≥0∞) * ∫⁻ ω in {ω | lam ≤ Mstar ω}, ENNReal.ofReal |M (Fin.last N) ω| ∂P =
        ∫⁻ ω, {q : ℝ × Ω | q.1 ≤ Mstar q.2}.indicator
          (fun q => ENNReal.ofReal (2 * |M (Fin.last N) q.2|)) (lam, ω) ∂P := fun lam => by
      rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ ENNReal.ofNat_ne_top,
        ← lintegral_indicator (measurableSet_le measurable_const hMstar_meas)]
      congr 1; funext ω
      by_cases h : lam ≤ Mstar ω
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    simp_rw [hrew]
    have hmeas_ind : Measurable (fun p : ℝ × Ω =>
        {q : ℝ × Ω | q.1 ≤ Mstar q.2}.indicator
          (fun q => ENNReal.ofReal (2 * |M (Fin.last N) q.2|)) p) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul ((hM_amb (Fin.last N)).abs.comp measurable_snd))).indicator
        (measurableSet_le measurable_fst (hMstar_meas.comp measurable_snd))
    rw [lintegral_lintegral_swap hmeas_ind.aemeasurable]
    refine lintegral_congr fun ω => ?_
    have heq : ∫⁻ lam in Ioi (0 : ℝ), {q : ℝ × Ω | q.1 ≤ Mstar q.2}.indicator
          (fun q => ENNReal.ofReal (2 * |M (Fin.last N) q.2|)) (lam, ω) ∂volume =
        ∫⁻ _lam in Ioc 0 (Mstar ω), ENNReal.ofReal (2 * |M (Fin.last N) ω|) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
      congr 1; funext lam
      by_cases h1 : 0 < lam <;> by_cases h2 : lam ≤ Mstar ω <;> simp [Set.indicator, h1, h2]
    rw [heq, setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * |M (Fin.last N) ω|)]
  have h2_le : ∫ ω, Mstar ω ^ 2 ∂P ≤ 2 * ∫ ω, |M (Fin.last N) ω| * |Mstar ω| ∂P := by
    have hprod_int : Integrable (fun ω => 2 * |M (Fin.last N) ω| * Mstar ω) P :=
      ((integrable_mul_of_memLp_two (hM_L2 (Fin.last N)).abs hMstar_L2).const_mul 2).congr
        (ae_of_all _ fun ω => by simp only [Pi.abs_apply]; ring)
    have hlint_ineq : ∫⁻ ω, ENNReal.ofReal (Mstar ω ^ 2) ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (2 * |M (Fin.last N) ω| * Mstar ω) ∂P := by
      rw [hlayer_L, ← hlayer_R]
      refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun lam hlam => ?_)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
      exact mul_le_mul' le_rfl (hweak lam hlam)
    have hnn_prod : ∀ ω, 0 ≤ 2 * |M (Fin.last N) ω| * Mstar ω := fun ω =>
      mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (hMstar_nn ω)
    have hreal : ∫ ω, Mstar ω ^ 2 ∂P ≤ ∫ ω, 2 * |M (Fin.last N) ω| * Mstar ω ∂P := by
      rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg hnn_prod),
        ofReal_integral_eq_lintegral_ofReal hMstar_L2.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
        ofReal_integral_eq_lintegral_ofReal hprod_int (ae_of_all _ hnn_prod)]
      exact hlint_ineq
    refine hreal.trans_eq ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => by dsimp only; rw [abs_of_nonneg (hMstar_nn ω)]; ring)
  have hcs := integral_mul_le_sqrt_mul_sqrt (hM_L2 (Fin.last N)) hMstar_L2
  set a := Real.sqrt (∫ ω, Mstar ω ^ 2 ∂P)
  set b := Real.sqrt (∫ ω, M (Fin.last N) ω ^ 2 ∂P)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ∫ ω, Mstar ω ^ 2 ∂P := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hb2 : b ^ 2 = ∫ ω, M (Fin.last N) ω ^ 2 ∂P := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hab : a ^ 2 ≤ 2 * (b * a) := by linarith
  have ha_le : a ≤ 2 * b := by
    by_cases ha_eq : a = 0
    · linarith [Real.sqrt_nonneg (∫ ω, M (Fin.last N) ω ^ 2 ∂P)]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha_eq)
      nlinarith
  rw [← ha2, ← hb2]; nlinarith

/-! ## Section 2: `L²` Helpers & Riemann-Prime Orthogonality Bound -/

private lemma jointElem_ito_meas {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (U : JointElem B T) {t : ℝ} (ht0 : 0 ≤ t) (_htT : t ≤ T) :
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

private lemma jointElem_ito_memLp {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
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

/-- `L²` convergence in `ℝ≥0∞` implies `TendstoInMeasure`. -/
lemma tendstoInMeasure_of_tendsto_lintegral_sq {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : AEStronglyMeasurable g P)
    (hlim : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop g := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · have hemp : ∀ n, {ω | (⊤ : ℝ≥0∞) ≤ edist (f n ω) (g ω)} = ∅ := fun n =>
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω =>
        not_le.mpr (edist_lt_top (f n ω) (g ω)) hω
    simp [hemp]
  · rw [ENNReal.tendsto_atTop_zero]; intro δ hδ
    have hε2_pos : (0 : ℝ≥0∞) < ε ^ 2 := by rw [sq]; exact ENNReal.mul_pos hε.ne' hε.ne'
    have hε2_top : ε ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hε_top
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) (ε ^ 2 * δ)
      (ENNReal.mul_pos hε2_pos.ne' hδ.ne')
    refine ⟨N, fun n hn => ?_⟩
    have hsub : {ω | ε ≤ edist (f n ω) (g ω)} ⊆
        {ω | ε ^ 2 ≤ ENNReal.ofReal ((f n ω - g ω) ^ 2)} := fun ω hω => by
      have hed : edist (f n ω) (g ω) = ENNReal.ofReal |f n ω - g ω| := by
        rw [edist_dist, Real.dist_eq]
      have hsq : ENNReal.ofReal ((f n ω - g ω) ^ 2) = edist (f n ω) (g ω) ^ 2 := by
        rw [hed, ← sq_abs (f n ω - g ω), ENNReal.ofReal_pow (abs_nonneg _)]
      rw [Set.mem_setOf_eq, hsq, sq, sq]; exact mul_le_mul' hω hω
    have haesm : AEMeasurable (fun ω => ENNReal.ofReal ((f n ω - g ω) ^ 2)) P :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).comp_aemeasurable ((hf n).sub hg).aemeasurable
    have hmarkov := mul_meas_ge_le_lintegral₀ haesm (ε ^ 2)
    have h1 : ε ^ 2 * P {ω | ε ≤ edist (f n ω) (g ω)} ≤ ε ^ 2 * δ :=
      (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmarkov.trans (hN n hn))
    exact (ENNReal.mul_le_mul_iff_right hε2_pos.ne' hε2_top).mp h1

/-- Orthogonality + `u`-cancellation bound on `itoRiemannPrime` for ANY `predSigma`-measurable `D`. -/
lemma lintegral_riemannPrime_sq_le {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T) {D : ℝ → Ω → ℝ}
    (hDp : IsPredictableProcess (pathFiltration B).σAlg T D) (n : ℕ) :
    ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd D t n ω ^ 2) ∂P ∂volume ≤
      ENNReal.ofReal (2 * T) * ∫⁻ p, ENNReal.ofReal (D p.1 p.2 ^ 2) ∂(dtP P T) := by
  have hstep_t : ∀ t ∈ Icc 0 T,
      ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd D t n ω ^ 2) ∂P ≤
      ∑ i ∈ Finset.Ico 1 (n + 1),
        (∫⁻ ω, ENNReal.ofReal (D ((i : ℝ) * t / ((n : ℝ) + 1)) ω ^ 2) ∂P) *
          ENNReal.ofReal (t / ((n : ℝ) + 1)) := fun t ht => by
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T := ht.2
    let DL (L : ℕ) (s : ℝ) (ω : Ω) : ℝ := max (-(L : ℝ)) (min (L : ℝ) (D s ω))
    have hDL_le : ∀ L s ω, |DL L s ω| ≤ (L : ℝ) := fun L s ω =>
      abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) L]) (min_le_left _ _)⟩
    have hDL_sq_le : ∀ L s ω, DL L s ω ^ 2 ≤ D s ω ^ 2 := fun L s ω => by
      rw [← sq_abs (DL L s ω), ← sq_abs (D s ω)]
      refine pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨?_, ?_⟩) 2
      · exact le_max_of_le_right (le_min (by linarith [Nat.cast_nonneg (α := ℝ) L, abs_nonneg (D s ω)]) (neg_abs_le _))
      · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) L, abs_nonneg (D s ω)]) ((min_le_right _ _).trans (le_abs_self _))
    have hDL_meas_slice : ∀ L (i : ℕ), i ≤ n + 1 →
        Measurable[(pathFiltration B).σAlg ((i : ℝ) * t / ((n : ℝ) + 1))]
          (DL L ((i : ℝ) * t / ((n : ℝ) + 1))) := fun L i hi => by
      have hslice := measurable_slice_of_predSigma
        (fun s r _ hsr _ => (pathFiltration B).mono hsr) hDp
        (s := (i : ℝ) * t / ((n : ℝ) + 1)) (by positivity) (by
          rw [div_le_iff₀ (by positivity)]
          have : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hi
          nlinarith)
      exact measurable_const.max (measurable_const.min hslice)
    have hlim_L : ∀ ω, Tendsto (fun L : ℕ => itoRiemannPrime B hd (DL L) t n ω ^ 2) atTop
        (𝓝 (itoRiemannPrime B hd D t n ω ^ 2)) := fun ω => by
      refine tendsto_atTop_of_eventually_const (i₀ := ∑ i ∈ Finset.Ico 1 (n + 1),
        ⌈|D ((i : ℝ) * t / ((n : ℝ) + 1)) ω|⌉₊) fun L hL => ?_
      congr 1; refine Finset.sum_congr rfl fun i hi => ?_
      have hle : |D ((i : ℝ) * t / ((n : ℝ) + 1)) ω| ≤ (L : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hL)
      have hEq : DL L ((i : ℝ) * t / ((n : ℝ) + 1)) ω = D ((i : ℝ) * t / ((n : ℝ) + 1)) ω := by
        unfold DL
        rw [min_eq_right ((le_abs_self _).trans hle), max_eq_right (by linarith [neg_abs_le (D ((i : ℝ) * t / ((n : ℝ) + 1)) ω)])]
      rw [hEq]
    have hbound_L : ∀ L : ℕ,
        ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (DL L) t n ω ^ 2) ∂P ≤
        ∑ i ∈ Finset.Ico 1 (n + 1),
          (∫⁻ ω, ENNReal.ofReal (D ((i : ℝ) * t / ((n : ℝ) + 1)) ω ^ 2) ∂P) *
            ENNReal.ofReal (t / ((n : ℝ) + 1)) := fun L => by
      let G : SortedElem B T :=
        { m := n + 2
          pts := fun k => if k.1 ≤ n + 1 then (k.1 : ℝ) * t / ((n : ℝ) + 1) else T
          c := fun k ω => if k.1 = 0 ∨ n + 1 ≤ k.1 then 0 else DL L ((k.1 : ℝ) * t / ((n : ℝ) + 1)) ω
          h0 := by simp
          hT := by simp
          hmono := fun k => by
            dsimp only [Fin.val_castSucc, Fin.val_succ]
            by_cases h1 : k.1 + 1 ≤ n + 1
            · have h0 : k.1 ≤ n + 1 := by omega
              simp only [h0, h1, ↓reduceIte]
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht0) (by positivity)
            · by_cases h0 : k.1 ≤ n + 1
              · simp only [h0, h1, ↓reduceIte]
                rw [div_le_iff₀ (by positivity)]
                have hk : (k.1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h0
                nlinarith
              · simp only [h0, h1, ↓reduceIte, le_rfl]
          hc_meas := fun k => by
            by_cases hc : k.1 = 0 ∨ n + 1 ≤ k.1
            · simp only [hc, ↓reduceIte]; exact measurable_const
            · have hk_le : k.1 ≤ n + 1 := by omega
              have hσ : (if (k.castSucc : ℕ) ≤ n + 1 then
                    (k.castSucc : ℝ) * t / ((n : ℝ) + 1) else T) =
                  (k.1 : ℝ) * t / ((n : ℝ) + 1) := by
                simp [Fin.coe_castSucc, hk_le]
              simp only [hc, ↓reduceIte]
              rw [hσ]
              exact hDL_meas_slice L k.1 hk_le
          hc_bdd := fun k => ⟨(L : ℝ), fun ω => by
            split_ifs
            · rw [abs_zero]; exact Nat.cast_nonneg L
            · exact hDL_le L _ ω⟩ }
      have hG_ito : ∀ ω, G.ito hd t ω = itoRiemannPrime B hd (DL L) t n ω := fun ω => by
        unfold SortedElem.ito itoRiemannPrime
        let g : ℕ → ℝ := fun k => if hk : k < n + 2 then
          G.c ⟨k, hk⟩ ω *
            (MultiBrownian.W B (min (G.pts (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (n + 3))) t) ω (kitDriver hd) -
             MultiBrownian.W B (min (G.pts (⟨k, Nat.lt_succ_of_lt hk⟩ : Fin (n + 3))) t) ω (kitDriver hd)) else 0
        have hmatch : (∑ k : Fin G.m, G.c k ω *
            (MultiBrownian.W B (min (G.pts k.succ) t) ω (kitDriver hd) -
             MultiBrownian.W B (min (G.pts k.castSucc) t) ω (kitDriver hd))) =
            ∑ k ∈ Finset.range (n + 2), g k := by
          rw [← Fin.sum_univ_eq_sum_range g (n + 2)]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : (k : ℕ) < n + 2 := by
            change (k : ℕ) < G.m; exact k.isLt
          simp only [g, hk, ↓reduceDIte]
          first | rfl | (congr 1 <;> first
            | (congr 1; exact Fin.eta k)
            | (congr 2 <;> (apply Fin.ext; simp [Fin.val_succ, Fin.coe_castSucc])))
        rw [hmatch]
        have hsub : Finset.Ico 1 (n + 1) ⊆ Finset.range (n + 2) := fun k hk => by
          rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_Ico.mp hk
          have hk_lt : k < n + 2 := by omega
          have hk1 : k + 1 ≤ n + 1 := by omega
          have hk0 : k ≤ n + 1 := by omega
          have hnc : ¬ (k = 0 ∨ n + 1 ≤ k) := by omega
          have hmin1 : min (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t = ((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) :=
            min_eq_left (by
              rw [div_le_iff₀ (by positivity), mul_comm t]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) ht0)
          have hmin0 : min ((k : ℝ) * t / ((n : ℝ) + 1)) t = (k : ℝ) * t / ((n : ℝ) + 1) :=
            min_eq_left (by
              rw [div_le_iff₀ (by positivity), mul_comm t]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk0) ht0)
          simp only [g, hk_lt, ↓reduceDIte, G, hk1, hk0, hnc, ↓reduceIte, hmin1, hmin0]
        · intro k hk hnot
          have hk_lt : k < n + 2 := Finset.mem_range.mp hk
          have hc : k = 0 ∨ n + 1 ≤ k := by rw [Finset.mem_Ico] at hnot; omega
          simp only [g, hk_lt, ↓reduceDIte, G, hc, ↓reduceIte, zero_mul]
      have hG_sq := integral_sortedElem_ito_sq hd G ht0 htT
      have hG_int : Integrable (fun ω => itoRiemannPrime B hd (DL L) t n ω ^ 2) P := by
        have hrew : itoRiemannPrime B hd (DL L) t n = fun ω => ∑ i ∈ Finset.Ico 1 (n + 1),
            DL L ((i : ℝ) * t / ((n : ℝ) + 1)) ω *
              wnnIncr B (kitDriver hd) ((i : ℝ) * t / ((n : ℝ) + 1)) (((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω :=
          funext fun ω => Finset.sum_congr rfl fun i _ => by simp only [wnnIncr_eq_W]
        rw [hrew]
        refine (memLp_finsetSum (Finset.Ico 1 (n + 1)) fun i hi => ?_).integrable_sq
        have hi' := Finset.mem_Ico.mp hi
        have hW := (hasLaw_wnnIncr B (kitDriver hd)
          (a := (i : ℝ) * t / ((n : ℝ) + 1))
          (b := ((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1))
          (by positivity)
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Nat.le_succ i) : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ)) ht0)
            (by positivity))).memLp
          (memLp_id_gaussianReal' 2 (by simp))
        have hDm : Measurable (DL L ((i : ℝ) * t / ((n : ℝ) + 1))) :=
          (hDL_meas_slice L i hi'.2.le).mono ((pathFiltration B).le_ambient _) le_rfl
        refine (hW.abs.const_mul (L : ℝ)).mono
          (hDm.mul (measurable_wnnIncr B (kitDriver hd)
            ((i : ℝ) * t / ((n : ℝ) + 1))
            (((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)))).aestronglyMeasurable
          (ae_of_all _ fun ω => ?_)
        simp only [Real.norm_eq_abs, abs_mul, Pi.abs_apply, abs_abs]
        have hLabs : |(L : ℝ)| = (L : ℝ) := abs_of_nonneg (Nat.cast_nonneg (α := ℝ) L)
        rw [hLabs]
        exact mul_le_mul_of_nonneg_right (hDL_le L ((i : ℝ) * t / ((n : ℝ) + 1)) ω) (abs_nonneg _)
      rw [← ofReal_integral_eq_lintegral_ofReal hG_int (ae_of_all _ fun _ => sq_nonneg _)]
      simp_rw [← hG_ito]; rw [hG_sq]
      have hsum_eq : ∑ k : Fin G.m, (∫ ω, G.c k ω ^ 2 ∂P) * (min (G.pts k.succ) t - min (G.pts k.castSucc) t) =
          ∑ i ∈ Finset.Ico 1 (n + 1), (∫ ω, DL L ((i : ℝ) * t / ((n : ℝ) + 1)) ω ^ 2 ∂P) * (t / ((n : ℝ) + 1)) := by
        let term : ℕ → ℝ := fun k => if hk : k < G.m then
          (∫ ω, G.c ⟨k, hk⟩ ω ^ 2 ∂P) *
            (min (G.pts (⟨k + 1, Nat.succ_lt_succ (by simpa [SortedElem.m, G] using hk)⟩ : Fin (G.m + 1))) t -
             min (G.pts (⟨k, Nat.lt_succ_of_lt (by simpa [SortedElem.m, G] using hk)⟩ : Fin (G.m + 1))) t) else 0
        have hmatch : (∑ k : Fin G.m, (∫ ω, G.c k ω ^ 2 ∂P) * (min (G.pts k.succ) t - min (G.pts k.castSucc) t)) =
            ∑ k ∈ Finset.range G.m, term k := by
          rw [← Fin.sum_univ_eq_sum_range term G.m]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : (k : ℕ) < G.m := k.isLt
          simp only [term, hk, ↓reduceDIte]
          first | rfl | (congr 2 <;> first
            | (congr 1; exact Fin.eta k)
            | (congr 2 <;> (apply Fin.ext; simp [Fin.val_succ, Fin.coe_castSucc])))
        rw [hmatch]
        have hsub : Finset.Ico 1 (n + 1) ⊆ Finset.range G.m := fun i hi => by
          have := Finset.mem_Ico.mp hi; simp only [G, Finset.mem_range]; omega
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_Ico.mp hi
          have hi_lt : i < G.m := by simp only [G]; omega
          have hnc : ¬ (i = 0 ∨ n + 1 ≤ i) := by omega
          have hi1 : i + 1 ≤ n + 1 := by omega
          have hi0 : i ≤ n + 1 := by omega
          have hmin1 : min (((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t = ((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) :=
            min_eq_left (by
              rw [div_le_iff₀ (by positivity), mul_comm t]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi1) ht0)
          have hmin0 : min ((i : ℝ) * t / ((n : ℝ) + 1)) t = (i : ℝ) * t / ((n : ℝ) + 1) :=
            min_eq_left (by
              rw [div_le_iff₀ (by positivity), mul_comm t]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi0) ht0)
          simp only [term, hi_lt, ↓reduceDIte, G, hi1, hi0, hnc, ↓reduceIte, hmin1, hmin0]
          congr 1; push_cast; ring
        · intro i hi hnot
          have hi_lt : i < G.m := Finset.mem_range.mp hi
          have hc : i = 0 ∨ n + 1 ≤ i := by rw [Finset.mem_Ico] at hnot; simp only [G] at hi_lt; omega
          simp only [term, hi_lt, ↓reduceDIte, G, hc, ↓reduceIte, zero_pow two_ne_zero, integral_zero, zero_mul]
      rw [hsum_eq, ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity))]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [ENNReal.ofReal_mul (integral_nonneg fun _ => sq_nonneg _)]
      refine mul_le_mul' ?_ le_rfl
      have hi' := Finset.mem_Ico.mp hi
      have hDm : Measurable (DL L ((i : ℝ) * t / ((n : ℝ) + 1))) :=
        (hDL_meas_slice L i hi'.2.le).mono ((pathFiltration B).le_ambient _) le_rfl
      have hDi : Integrable (fun ω => DL L ((i : ℝ) * t / ((n : ℝ) + 1)) ω ^ 2) P :=
        (integrable_const ((L : ℝ) ^ 2)).mono (hDm.pow_const 2).aestronglyMeasurable
          (ae_of_all _ fun ω => by
            rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hDL_le L _ ω) 2)
      rw [ofReal_integral_eq_lintegral_ofReal hDi (ae_of_all _ fun _ => sq_nonneg _)]
      exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hDL_sq_le L _ ω)
    have hfat : ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd D t n ω ^ 2) ∂P ≤
        liminf (fun L : ℕ => ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (DL L) t n ω ^ 2) ∂P) atTop := by
      calc ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd D t n ω ^ 2) ∂P
          = ∫⁻ ω, liminf (fun L : ℕ => ENNReal.ofReal (itoRiemannPrime B hd (DL L) t n ω ^ 2)) atTop ∂P :=
            lintegral_congr fun ω => (ENNReal.tendsto_ofReal (hlim_L ω)).liminf_eq.symm
        _ ≤ liminf (fun L : ℕ => ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (DL L) t n ω ^ 2) ∂P) atTop :=
            lintegral_liminf_le' fun L => by
              refine (ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun i hi => ?_).pow_const 2)).aemeasurable
              have hi' := Finset.mem_Ico.mp hi
              have hDm : Measurable (DL L ((i : ℝ) * t / ((n : ℝ) + 1))) :=
                (hDL_meas_slice L i hi'.2.le).mono ((pathFiltration B).le_ambient _) le_rfl
              exact hDm.mul ((MultiBrownian.W_meas B _ _).sub (MultiBrownian.W_meas B _ _))
    exact hfat.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound_L))
  let h : ℝ → ℝ≥0∞ := fun u => ∫⁻ ω, ENNReal.ofReal (D u ω ^ 2) ∂P
  have hh_meas : Measurable h :=
    (ENNReal.measurable_ofReal.comp
      ((hDp.mono (predSigma_le_prod (T := T) fun s _ => (pathFiltration B).le_ambient s) le_rfl).pow_const 2)).lintegral_prod_right'
  calc ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd D t n ω ^ 2) ∂P ∂volume
      ≤ ∫⁻ t in Icc 0 T, (∑ i ∈ Finset.Ico 1 (n + 1),
          h ((i : ℝ) * t / ((n : ℝ) + 1)) * ENNReal.ofReal (t / ((n : ℝ) + 1))) ∂volume :=
        lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hstep_t)
    _ ≤ ENNReal.ofReal (2 * T) * ∫⁻ u in Icc 0 T, h u ∂volume := lintegral_riemann_sq_le hT hh_meas n
    _ = ENNReal.ofReal (2 * T) * ∫⁻ p, ENNReal.ofReal (D p.1 p.2 ^ 2) ∂(dtP P T) := by
        congr 1; unfold dtP h
        exact (lintegral_prod _ (ENNReal.measurable_ofReal.comp
          ((hDp.mono (predSigma_le_prod (T := T) fun s _ => (pathFiltration B).le_ambient s) le_rfl).pow_const 2)).aemeasurable).symm

/-! ## Section 3: Main Continuous L² Itô Integral & Subsequence Theorem -/


set_option maxHeartbeats 2000000

/-- Riemann-prime subsequence for a continuous L² Itô integral already constructed. -/
private lemma exists_riemann_subseq_from_contIto
    {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → ℝ}
    (hZp : IsPredictableProcess (pathFiltration B).σAlg T Z)
    (hW_jm : Measurable (fun p : ℝ × Ω => MultiBrownian.W B p.1 p.2 (kitDriver hd)))
    (hZL2 : MemLp (Function.uncurry Z) 2 (dtP P T))
    (U : ℕ → JointElem B T)
    (hU : ∀ k, ∫ p, (Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2 ∂(dtP P T) < (1 / 2 : ℝ) ^ (4 * k))
    (M : ℝ → Ω → ℝ)
    (hM_eq : ∀ t ω, M t ω = limUnder atTop fun k => (U k).ito hd t ω)
    (hM_meas : ∀ t ∈ Icc 0 T, Measurable[(pathFiltration B).σAlg t] (M t))
    (hM_L2 : ∀ t ∈ Icc 0 T,
      MemLp (M t) 2 P ∧ ∀ k, ∫ ω, (M t ω - (U k).ito hd t ω) ^ 2 ∂P ≤ 4 * (1 / 2 : ℝ) ^ (4 * k)) :
    ∃ (G : Set ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ volume (Ioo 0 T \ G) = 0 ∧
      ∀ t ∈ G ∩ Ioo 0 T,
        TendstoInMeasure P (fun j => itoRiemannPrime B hd Z t (φ j)) atTop (M t) := by
    have hU_ito_jm : ∀ k, Measurable (fun p : ℝ × Ω => (U k).ito hd p.1 p.2) := fun k =>
      Finset.measurable_sum _ fun j _ =>
        (((U k).h_meas j |>.mono ((pathFiltration B).le_ambient _) le_rfl).comp measurable_snd).mul
        ((hW_jm.comp ((measurable_const.min measurable_fst).prodMk measurable_snd)).sub
         (hW_jm.comp ((measurable_const.min measurable_fst).prodMk measurable_snd)))
    have hM_jm : Measurable (fun p : ℝ × Ω => M p.1 p.2) := by
      have hrew : (fun p : ℝ × Ω => M p.1 p.2) =
          fun p => limUnder atTop fun k => (U k).ito hd p.1 p.2 :=
        funext fun p => hM_eq p.1 p.2
      rw [hrew]
      exact (StronglyMeasurable.limUnder fun k => (hU_ito_jm k).stronglyMeasurable).measurable
    have hR_jm : ∀ (F : ℝ → Ω → ℝ) (hFp : IsPredictableProcess (pathFiltration B).σAlg T F) (n : ℕ),
        Measurable (fun p : ℝ × Ω => itoRiemannPrime B hd F p.1 n p.2) := fun F hFp n =>
      Finset.measurable_sum _ fun i _ =>
        ((hFp.mono (predSigma_le_prod (T := T) fun _ _ => (pathFiltration B).le_ambient _) le_rfl).comp
          (((measurable_const.mul measurable_fst).div_const _).prodMk measurable_snd)).mul
        ((hW_jm.comp (((measurable_const.mul measurable_fst).div_const _).prodMk measurable_snd)).sub
         (hW_jm.comp (((measurable_const.mul measurable_fst).div_const _).prodMk measurable_snd)))
    have hint_lim : Tendsto (fun n : ℕ => ∫⁻ t in Icc 0 T,
        ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P ∂volume) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_atTop_zero]; intro ε hε
      obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
        rcases eq_or_ne ε ⊤ with rfl | hne
        · exact ⟨1, one_pos, le_top⟩
        · exact ⟨ε.toReal / 2, half_pos (ENNReal.toReal_pos hε.ne' hne),
            (ENNReal.ofReal_le_ofReal (half_le_self ENNReal.toReal_nonneg)).trans_eq (ENNReal.ofReal_toReal hne)⟩
      have hdecay : Tendsto (fun k : ℕ => 18 * T * (1 / 2 : ℝ) ^ (4 * k)) atTop (𝓝 0) := by
        have hrew : (fun k : ℕ => 18 * T * (1 / 2 : ℝ) ^ (4 * k)) =
            fun k => 18 * T * (1 / 16 : ℝ) ^ k :=
          funext fun k => by rw [pow_mul]; norm_num
        rw [hrew]
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
          (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num)).const_mul (18 * T)
      obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hdecay) (δ / 2) (half_pos hδ_pos)
      have hk' : 18 * T * (1 / 2 : ℝ) ^ (4 * k) ≤ δ / 2 := by
        have := hk k le_rfl; rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this.le
      choose Cj hCj using (U k).h_bdd
      set C : ℝ := ∑ j : Fin (U k).n, max (Cj j) 0
      have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => le_max_right _ _
      have hC : ∀ j ω, |(U k).h j ω| ≤ C := fun j ω =>
        ((hCj j ω).trans (le_max_left _ _)).trans
          (Finset.single_le_sum (fun i _ => le_max_right (Cj i) 0) (Finset.mem_univ j))
      set Kconst : ℝ := 12 * (((U k).n : ℝ) * C) ^ 2 * ((2 * (U k).n + 1 : ℕ) : ℝ) * T ^ 2
      obtain ⟨N, hN⟩ := exists_nat_gt (Kconst / (δ / 2))
      refine ⟨N, fun n hn => ?_⟩
      have hsub_pred : IsPredictableProcess (pathFiltration B).σAlg T (fun s ω => Z s ω - (U k).toFun s ω) :=
        hZp.sub (U k).measurable_pred
      have hjm1 : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) p.1 n p.2 ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((hR_jm _ hsub_pred n).pow_const 2)
      have hjm2 : Measurable (fun p : ℝ × Ω => ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun p.1 n p.2 - (U k).ito hd p.1 p.2) ^ 2)) :=
        ENNReal.measurable_ofReal.comp (((hR_jm _ (U k).measurable_pred n).sub (hU_ito_jm k)).pow_const 2)
      have hsplit : ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P ∂volume ≤
          3 * (∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P ∂volume) +
          3 * (∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P ∂volume) +
          3 * (∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2) ∂P ∂volume) := by
        have hlin : ∀ t ω, itoRiemannPrime B hd Z t n ω - itoRiemannPrime B hd (U k).toFun t n ω =
            itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω := fun t ω => by
          unfold itoRiemannPrime; rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        have h3_t : ∀ t ∈ Icc 0 T,
            ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P ≤
            3 * ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P +
            3 * ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P +
            3 * ∫⁻ ω, ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2) ∂P := fun t _ => by
          have hm1 : Measurable (fun ω => ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2)) :=
            measurable_eval_prod _ hjm1 t
          have hm2 : Measurable (fun ω => ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2)) :=
            measurable_eval_prod _ hjm2 t
          calc ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P
              ≤ ∫⁻ ω, (3 * ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) +
                  3 * ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) +
                  3 * ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2)) ∂P := by
                refine lintegral_mono fun ω => ?_
                set x := itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω
                set y := itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω
                set z := (U k).ito hd t ω - M t ω
                have hxyz : itoRiemannPrime B hd Z t n ω - M t ω = x + y + z := by linarith [hlin t ω]
                have hpt : (itoRiemannPrime B hd Z t n ω - M t ω) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
                  rw [hxyz]; nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
                refine (ENNReal.ofReal_le_ofReal hpt).trans_eq ?_
                rw [ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
                  ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            _ = _ := by
                rw [lintegral_add_left
                      (f := fun ω =>
                        3 * ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) +
                        3 * ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2))
                      ((hm1.const_mul 3).add (hm2.const_mul 3)),
                    lintegral_add_left
                      (f := fun ω =>
                        3 * ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2))
                      (hm1.const_mul 3),
                    lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top,
                    lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top,
                    lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top]
        calc ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P ∂volume
            ≤ ∫⁻ t in Icc 0 T, (3 * ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P +
                3 * ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P +
                3 * ∫⁻ ω, ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2) ∂P) ∂volume :=
              lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc h3_t)
          _ = _ := by
              rw [lintegral_add_left
                    (f := fun t =>
                      3 * ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P +
                      3 * ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P)
                    ((hjm1.lintegral_prod_right'.const_mul 3).add (hjm2.lintegral_prod_right'.const_mul 3)),
                  lintegral_add_left
                    (f := fun t =>
                      3 * ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P)
                    (hjm1.lintegral_prod_right'.const_mul 3),
                  lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top,
                  lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top,
                  lintegral_const_mul' 3 _ ENNReal.ofNat_ne_top]
      -- Term 1 ≤ `6 T 2^(-4k)` via `lintegral_riemannPrime_sq_le`
      have hb1 : 3 * ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (itoRiemannPrime B hd (fun s ω => Z s ω - (U k).toFun s ω) t n ω ^ 2) ∂P ∂volume ≤
          ENNReal.ofReal (6 * T * (1 / 2 : ℝ) ^ (4 * k)) := by
        have h1 := lintegral_riemannPrime_sq_le hd B hT hsub_pred n
        have h2 : ∫⁻ p, ENNReal.ofReal ((Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2) ∂(dtP P T) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * k)) := by
          have hi_sub : Integrable (fun p : ℝ × Ω => (Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2) (dtP P T) :=
            (hZL2.sub (U k).memLp_dtP).integrable_sq
          rw [← ofReal_integral_eq_lintegral_ofReal hi_sub (ae_of_all _ fun _ => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hU k).le
        calc 3 * _ ≤ 3 * (ENNReal.ofReal (2 * T) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * k))) :=
              mul_le_mul' le_rfl (h1.trans (mul_le_mul' le_rfl h2))
          _ = ENNReal.ofReal (6 * T * (1 / 2 : ℝ) ^ (4 * k)) := by
              rw [← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      -- Term 2 ≤ `Kconst / (n + 1) ≤ δ / 2` via `integral_itoRiemannPrime_jointElem_sub_sq_le`
      have hb2 : 3 * ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P ∂volume ≤
          ENNReal.ofReal (δ / 2) := by
        have hpt : ∀ t ∈ Icc 0 T,
            ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) ∂P ≤
            ENNReal.ofReal ((4 * (((U k).n : ℝ) * C) ^ 2 * ((2 * (U k).n + 1 : ℕ) : ℝ) * T) / ((n : ℝ) + 1)) := fun t ht => by
          have ht0 : 0 ≤ t := ht.1
          have htT : t ≤ T := ht.2
          have hi : Integrable (fun ω => (itoRiemannPrime B hd (U k).toFun t n ω - (U k).ito hd t ω) ^ 2) P := by
            let Un : JointElem B T :=
              { n := n, a := fun i => ((i.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1),
                b := fun i => ((i.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1),
                h := fun i ω => (U k).toFun (((i.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω,
                hab := fun i => ⟨by positivity,
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht0) (by positivity),
                  by rw [div_le_iff₀ (by positivity)]
                     have : ((i.1 + 2 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ i.isLt)
                     nlinarith⟩,
                h_meas := fun i => measurable_slice_of_predSigma (fun _ _ _ hsr _ => (pathFiltration B).mono hsr)
                  (U k).measurable_pred (s := ((i.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) (by positivity)
                  (by rw [div_le_iff₀ (by positivity)]
                      have : ((i.1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ i.isLt.le)
                      nlinarith),
                h_bdd := fun i => ⟨((U k).n : ℝ) * C, fun ω =>
                  (Finset.abs_sum_le_sum_abs (f := fun j : Fin (U k).n => if (U k).a j < ((i.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ∧
                    ((i.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ (U k).b j then (U k).h j ω else 0) Finset.univ).trans
                    (by calc _ ≤ ∑ _j : Fin (U k).n, C := Finset.sum_le_sum fun j _ => by split_ifs; exact hC j ω; rw [abs_zero]; exact hC0
                      _ = ((U k).n : ℝ) * C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])⟩ }
            have hUn_eq : ∀ ω, Un.ito hd t ω = itoRiemannPrime B hd (U k).toFun t n ω := fun ω => by
              unfold JointElem.ito itoRiemannPrime
              rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
              let f : ℕ → ℝ := fun i => (U k).toFun (((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω *
                (MultiBrownian.W B (min (((i + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t) ω (kitDriver hd) -
                 MultiBrownian.W B (min (((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t) ω (kitDriver hd))
              change (∑ i : Fin n, f i.1) = _
              rw [Fin.sum_univ_eq_sum_range f n]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hi' := Finset.mem_range.mp hi
              have h1 : ((i + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ t := by
                rw [div_le_iff₀ (by positivity)]
                have : ((i + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ hi'.le)
                nlinarith
              have h2 : ((i + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ t := by
                rw [div_le_iff₀ (by positivity)]
                have : ((i + 2 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hi')
                nlinarith
              simp only [f, min_eq_left h1, min_eq_left h2, add_comm 1 i, show i + 1 + 1 = i + 2 by omega]
            exact ((jointElem_ito_memLp hd Un ht0).sub (jointElem_ito_memLp hd (U k) ht0)).integrable_sq.congr
              (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; rw [hUn_eq])
          rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ((integral_itoRiemannPrime_jointElem_sub_sq_le hd hT (U k) C hC hC0 ht0 htT n).trans ?_)
          gcongr
        calc 3 * _ ≤ 3 * (ENNReal.ofReal ((4 * (((U k).n : ℝ) * C) ^ 2 * ((2 * (U k).n + 1 : ℕ) : ℝ) * T) / ((n : ℝ) + 1)) * volume (Icc 0 T)) :=
              mul_le_mul' le_rfl ((lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hpt)).trans_eq (setLIntegral_const _ _))
          _ = ENNReal.ofReal (Kconst / ((n : ℝ) + 1)) := by
              rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_ofNat (n := 3),
                ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1; simp only [Kconst]; ring
          _ ≤ ENNReal.ofReal (δ / 2) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [div_le_iff₀ (by positivity)]
              have hlt : Kconst / (δ / 2) < (n : ℝ) + 1 := lt_of_lt_of_le hN (by exact_mod_cast hn.trans (Nat.le_succ n))
              linarith [(div_lt_iff₀ (half_pos hδ_pos)).mp hlt]
      -- Term 3 ≤ `12 T 2^(-4k)` via `hM_L2`
      have hb3 : 3 * ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2) ∂P ∂volume ≤
          ENNReal.ofReal (12 * T * (1 / 2 : ℝ) ^ (4 * k)) := by
        have hpt : ∀ t ∈ Icc 0 T,
            ∫⁻ ω, ENNReal.ofReal (((U k).ito hd t ω - M t ω) ^ 2) ∂P ≤ ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ (4 * k)) := fun t ht => by
          have hi : Integrable (fun ω => ((U k).ito hd t ω - M t ω) ^ 2) P :=
            ((jointElem_ito_memLp hd (U k) ht.1).sub (hM_L2 t ht).1).integrable_sq
          rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (fun ω => ((U k).ito hd t ω - M t ω) ^ 2) = fun ω => (M t ω - (U k).ito hd t ω) ^ 2 from funext fun _ => by ring]
          exact (hM_L2 t ht).2 k
        calc 3 * _ ≤ 3 * (ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ (4 * k)) * volume (Icc 0 T)) :=
              mul_le_mul' le_rfl ((lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hpt)).trans_eq (setLIntegral_const _ _))
          _ = ENNReal.ofReal (12 * T * (1 / 2 : ℝ) ^ (4 * k)) := by
              rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_ofNat (n := 3),
                ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1; ring
      calc _ ≤ ENNReal.ofReal (6 * T * (1 / 2 : ℝ) ^ (4 * k)) + ENNReal.ofReal (δ / 2) +
              ENNReal.ofReal (12 * T * (1 / 2 : ℝ) ^ (4 * k)) := hsplit.trans (add_le_add (add_le_add hb1 hb2) hb3)
        _ = ENNReal.ofReal (18 * T * (1 / 2 : ℝ) ^ (4 * k) + δ / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ε := hδ_lt
    -- Extract strictly increasing `φ` with `∫⁻ t, ∫⁻ ω, (R'_{φ j}(Z) - M)² ≤ (1/2)^j` ⇒ `tsum < ⊤` a.e. in `t`!
    have hexN : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        ∫⁻ t in Icc 0 T, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t n ω - M t ω) ^ 2) ∂P ∂volume ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := fun j =>
      (ENNReal.tendsto_atTop_zero.mp hint_lim) (ENNReal.ofReal ((1 / 2 : ℝ) ^ j)) (ENNReal.ofReal_pos.mpr (by positivity))
    choose Nf hNf using hexN
    let φ : ℕ → ℕ := fun j => Nat.rec (Nf 0) (fun k prev => max (prev + 1) (Nf (k + 1))) j
    have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun k => Nat.lt_of_succ_le (le_max_left _ _)
    have hφ_ge : ∀ j, Nf j ≤ φ j := fun j => by cases j with | zero => exact le_rfl | succ k => exact le_max_right _ _
    let G : Set ℝ := {t | ∑' j : ℕ, ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t (φ j) ω - M t ω) ^ 2) ∂P < ⊤}
    have hterm_m : ∀ j, AEMeasurable (fun t : ℝ =>
        ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t (φ j) ω - M t ω) ^ 2) ∂P) (volume.restrict (Icc 0 T)) := fun j =>
      (ENNReal.measurable_ofReal.comp (((hR_jm Z hZp (φ j)).sub hM_jm).pow_const 2)).lintegral_prod_right'.aemeasurable
    have htsum_fin : ∫⁻ t in Icc 0 T, ∑' j : ℕ,
        ∫⁻ ω, ENNReal.ofReal ((itoRiemannPrime B hd Z t (φ j) ω - M t ω) ^ 2) ∂P ∂volume ≠ ⊤ := by
      rw [lintegral_tsum hterm_m]
      exact ne_top_of_le_ne_top summable_geometric_two.tsum_ofReal_ne_top
        (ENNReal.tsum_le_tsum fun j => hNf j (φ j) (hφ_ge j))
    refine ⟨G, φ, hφ_mono, ?_, ?_⟩
    · show volume (Ioo 0 T \ G) = 0
      have hae : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), t ∈ G :=
        ae_lt_top' (AEMeasurable.tsum hterm_m) htsum_fin
      rw [ae_iff, Measure.restrict_apply' measurableSet_Icc] at hae
      refine measure_mono_null (s := Ioo 0 T \ G)
        (t := {u : ℝ | u ∉ G} ∩ Icc 0 T) ?_ hae
      intro u hu
      exact And.intro hu.2 (Ioo_subset_Icc_self hu.1)
    · intro t ht
      have htG : t ∈ G := ht.1
      have htIoo : t ∈ Ioo 0 T := ht.2
      have htIcc : t ∈ Icc 0 T := Ioo_subset_Icc_self htIoo
      refine tendstoInMeasure_of_tendsto_lintegral_sq
        (fun j => (Finset.measurable_sum _ fun i hi => by
          have hi' := Finset.mem_Ico.mp hi
          have ht0 := htIcc.1
          have hZm := (measurable_slice_of_predSigma (fun _ _ _ hsr _ => (pathFiltration B).mono hsr) hZp
            (s := (i : ℝ) * t / ((φ j : ℝ) + 1)) (by positivity) (by
              rw [div_le_iff₀ (by positivity)]
              have : (i : ℝ) ≤ (φ j : ℝ) + 1 := by exact_mod_cast hi'.2.le
              nlinarith [htIcc.2])).mono ((pathFiltration B).le_ambient _) le_rfl
          exact hZm.mul ((MultiBrownian.W_meas B _ _).sub (MultiBrownian.W_meas B _ _))).aestronglyMeasurable)
        ((hM_meas t htIcc).mono ((pathFiltration B).le_ambient t) le_rfl).aestronglyMeasurable
        (ENNReal.tendsto_atTop_zero_of_tsum_ne_top htG.ne)

set_option maxHeartbeats 2000000

/-- Pathwise: the squared dyadic-grid supremum of a JointElem Itô increment
tends to the squared pathwise supremum on `[0, T]`. -/
private lemma tendsto_ito_increment_dyadic_sup
    {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T)
    (U : ℕ → JointElem B T)
    (hU_cont : ∀ k ω, Continuous (fun t => (U k).ito hd t ω))
    (k : ℕ) (ω : Ω) :
    Tendsto (fun m : ℕ => ENNReal.ofReal ((Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i : Fin (2 ^ m + 1) => |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
          (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|)) ^ 2))
      atTop (𝓝 (ENNReal.ofReal ((⨆ t : {t : ℝ // t ∈ Icc 0 T},
        |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ^ 2))) := by
    have : Nonempty {t : ℝ // t ∈ Icc 0 T} := ⟨⟨0, le_rfl, hT.le⟩⟩
    have hcont : Continuous (fun t => |(U (k + 1)).ito hd t ω - (U k).ito hd t ω|) :=
      ((hU_cont (k + 1) ω).sub (hU_cont k ω)).abs
    obtain ⟨t0, ht0I, ht0_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT.le⟩ hcont.continuousOn
    have hsup_eq : (⨆ t : {t : ℝ // t ∈ Icc 0 T}, |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) =
        |(U (k + 1)).ito hd t0 ω - (U k).ito hd t0 ω| := by
      refine le_antisymm ?_ ?_
      · exact ciSup_le (fun t : {t : ℝ // t ∈ Icc 0 T} => ht0_max t.property)
      · refine le_ciSup (f := fun t : {t : ℝ // t ∈ Icc 0 T} =>
            |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ?_ ⟨t0, ht0I⟩
        refine ⟨|(U (k + 1)).ito hd t0 ω - (U k).ito hd t0 ω|, ?_⟩
        rintro _ ⟨(t : {t : ℝ // t ∈ Icc 0 T}), rfl⟩
        exact ht0_max t.property
    rw [hsup_eq]
    let fgrid : ℕ → ℝ := fun m =>
      |(U (k + 1)).ito hd ((⌊t0 / T * 2 ^ m⌋₊ : ℝ) * T / (2 ^ m : ℝ)) ω -
        (U k).ito hd ((⌊t0 / T * 2 ^ m⌋₊ : ℝ) * T / (2 ^ m : ℝ)) ω|
    let hdisc : ℕ → ℝ := fun m =>
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i : Fin (2 ^ m + 1) =>
          |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
            (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|)
    let gmax : ℕ → ℝ := fun _ =>
      |(U (k + 1)).ito hd t0 ω - (U k).ito hd t0 ω|
    refine ENNReal.tendsto_ofReal
      ((tendsto_of_tendsto_of_tendsto_of_le_of_le
          (f := hdisc) (g := fgrid) (h := gmax) (b := atTop)
          ?_ tendsto_const_nhds ?_ ?_).pow 2)
    · have hlim_pt : Tendsto (fun m : ℕ => ((⌊t0 / T * 2 ^ m⌋₊ : ℝ) * T / (2 ^ m : ℝ))) atTop (𝓝 t0) := by
        have h0 : Tendsto (fun m : ℕ => T / (2 ^ m : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using tendsto_const_nhds.sub h0) tendsto_const_nhds
          (fun m => by
            have hlt := Nat.lt_floor_add_one (t0 / T * 2 ^ m)
            rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ (by positivity)]
            have := mul_le_mul_of_nonneg_right hlt.le hT.le
            have : t0 / T * 2 ^ m * T = t0 * 2 ^ m := by field_simp
            linarith)
          (fun m => by
            rw [div_le_iff₀ (by positivity)]
            have hle := Nat.floor_le (by have := ht0I.1; positivity : 0 ≤ t0 / T * 2 ^ m)
            have := mul_le_mul_of_nonneg_right hle hT.le
            have : t0 / T * 2 ^ m * T = t0 * 2 ^ m := by field_simp
            linarith)
      exact (hcont.tendsto t0).comp hlim_pt
    · intro m
      change fgrid m ≤ hdisc m
      have hidx : ⌊t0 / T * 2 ^ m⌋₊ < 2 ^ m + 1 := Nat.lt_succ_of_le (Nat.floor_le_of_le <| by
        have : t0 / T ≤ 1 := (div_le_one hT).mpr ht0I.2; push_cast; nlinarith [show (0 : ℝ) < (2 : ℝ) ^ m by positivity])
      have hmem : (⟨⌊t0 / T * 2 ^ m⌋₊, hidx⟩ : Fin (2 ^ m + 1)) ∈ Finset.univ :=
        Finset.mem_univ _
      convert (Finset.le_sup'
        (fun i : Fin (2 ^ m + 1) =>
          |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
            (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|) hmem)
    · intro m; refine Finset.sup'_le _ _ fun i _ => ht0_max ⟨by positivity, by
        rw [div_le_iff₀ (by positivity), mul_comm T]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hT.le⟩

set_option maxHeartbeats 2000000

/-- Doob's L² maximal inequality on the dyadic grid for a JointElem Itô increment. -/
private lemma ito_increment_dyadic_sup_L2_le
    {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T)
    (U : ℕ → JointElem B T)
    (hU_ito_L2_diff : ∀ k₁ k₂, ∀ t ∈ Icc 0 T,
      ∫ ω, ((U k₁).ito hd t ω - (U k₂).ito hd t ω) ^ 2 ∂P ≤
        2 * (1 / 2 : ℝ) ^ (4 * k₁) + 2 * (1 / 2 : ℝ) ^ (4 * k₂))
    (k m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.sup' Finset.univ Finset.univ_nonempty
      (fun i : Fin (2 ^ m + 1) => |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
        (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|)) ^ 2) ∂P ≤
      ENNReal.ofReal (16 * (1 / 2 : ℝ) ^ (4 * k)) := by
    let grid : Fin (2 ^ m + 1) → ℝ := fun i => (i : ℝ) * T / (2 ^ m : ℝ)
    have hgm : ∀ i, grid i ∈ Icc 0 T := fun i => ⟨by simp only [grid]; positivity, by
      simp only [grid]; rw [div_le_iff₀ (by positivity), mul_comm T]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hT.le⟩
    have hdoob := doob_l2_maximal_discrete (N := 2 ^ m) (𝒢 := fun i => (pathFiltration B).σAlg (grid i))
      (fun i j hij => (pathFiltration B).mono (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hT.le) (by positivity)))
      (fun i => (pathFiltration B).le_ambient (grid i))
      (fun i ω => (U (k + 1)).ito hd (grid i) ω - (U k).ito hd (grid i) ω)
      (fun i => (jointElem_ito_meas hd (U (k + 1)) (hgm i).1 (hgm i).2).sub
        (jointElem_ito_meas hd (U k) (hgm i).1 (hgm i).2))
      (fun i => (jointElem_ito_memLp hd (U (k + 1)) (hgm i).1).sub (jointElem_ito_memLp hd (U k) (hgm i).1))
      (fun i A hA => by
        have hlast : grid (Fin.last (2 ^ m)) = T := by
          simp only [grid, Fin.val_last]
          field_simp
          norm_cast
        rw [hlast]
        have h1 := setIntegral_jointElem_ito hd ((U (k + 1)).add (U k).neg) (hgm i).1 (hgm i).2 le_rfl hA
        simpa [JointElem.add_ito, JointElem.neg_ito, sub_eq_add_neg] using h1)
    rw [← ofReal_integral_eq_lintegral_ofReal hdoob.1 (ae_of_all _ fun _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hdoob.2.trans ?_)
    have hlast : grid (Fin.last (2 ^ m)) = T := by
      simp only [grid, Fin.val_last]
      field_simp
      norm_cast
    rw [hlast]
    have hpow : (1 / 2 : ℝ) ^ (4 * (k + 1)) ≤ (1 / 2 : ℝ) ^ (4 * k) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hU_ito_L2_diff (k + 1) k T ⟨hT.le, le_rfl⟩]

set_option maxHeartbeats 2000000

/-- L² bound on the pathwise supremum of a JointElem Itô increment. -/
private lemma ito_increment_sup_L2_le
    {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    {T : ℝ} (hT : 0 < T)
    (U : ℕ → JointElem B T)
    (hU_cont : ∀ k ω, Continuous (fun t => (U k).ito hd t ω))
    (hU_ito_L2_diff : ∀ k₁ k₂, ∀ t ∈ Icc 0 T,
      ∫ ω, ((U k₁).ito hd t ω - (U k₂).ito hd t ω) ^ 2 ∂P ≤
        2 * (1 / 2 : ℝ) ^ (4 * k₁) + 2 * (1 / 2 : ℝ) ^ (4 * k₂))
    (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((⨆ t : {t : ℝ // t ∈ Icc 0 T},
      |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ^ 2) ∂P ≤
      ENNReal.ofReal (16 * (1 / 2 : ℝ) ^ (4 * k)) := by
    have : Nonempty {t : ℝ // t ∈ Icc 0 T} := ⟨⟨0, le_rfl, hT.le⟩⟩
    refine le_of_tendsto_of_tendsto' (b := atTop)
      (f := fun m : ℕ => ∫⁻ ω, ENNReal.ofReal ((Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i : Fin (2 ^ m + 1) => |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
          (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|)) ^ 2) ∂P)
      (g := fun _ : ℕ => ENNReal.ofReal (16 * (1 / 2 : ℝ) ^ (4 * k)))
      ?_ tendsto_const_nhds fun m => ?_
    · refine lintegral_tendsto_of_tendsto_of_monotone
        (fun m => (ENNReal.measurable_ofReal.comp ((measurable_of_Iic fun c => by
          have : (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty
            (fun i : Fin (2 ^ m + 1) => |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
              (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω|)) ⁻¹' Iic c =
            ⋂ i : Fin (2 ^ m + 1), {ω | |(U (k + 1)).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω -
              (U k).ito hd ((i : ℝ) * T / (2 ^ m : ℝ)) ω| ≤ c} := by ext ω; simp [Finset.sup'_le_iff]
          rw [this]; exact MeasurableSet.iInter fun i => measurableSet_le
            (((jointElem_ito_meas hd (U (k + 1)) (by positivity) (by
                rw [div_le_iff₀ (by positivity), mul_comm T]
                exact mul_le_mul_of_nonneg_right
                  (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hT.le)).sub
              (jointElem_ito_meas hd (U k) (by positivity) (by
                rw [div_le_iff₀ (by positivity), mul_comm T]
                exact mul_le_mul_of_nonneg_right
                  (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hT.le))).mono
              ((pathFiltration B).le_ambient _) le_rfl).abs measurable_const).pow_const 2)).aemeasurable)
        (ae_of_all _ fun ω m₁ m₂ h12 => by
          refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Finset.le_sup'_of_le _ (Finset.mem_univ (0 : Fin _)) (abs_nonneg _)) ?_ 2)
          refine Finset.sup'_le _ _ fun i _ => ?_
          have hi_le : i.1 * 2 ^ (m₂ - m₁) < 2 ^ m₂ + 1 := by
            have : i.1 * 2 ^ (m₂ - m₁) ≤ 2 ^ m₁ * 2 ^ (m₂ - m₁) := Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt)
            rw [← pow_add, Nat.add_sub_cancel' h12] at this; omega
          refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ ⟨i.1 * 2 ^ (m₂ - m₁), hi_le⟩))
          have hgrid_eq : (i : ℝ) * T / (2 ^ m₁ : ℝ) = ((i.1 * 2 ^ (m₂ - m₁) : ℕ) : ℝ) * T / (2 ^ m₂ : ℝ) := by
            push_cast; rw [show (2 : ℝ) ^ m₂ = (2 : ℝ) ^ m₁ * (2 : ℝ) ^ (m₂ - m₁) by rw [← pow_add, Nat.add_sub_cancel' h12]]; field_simp
          rw [hgrid_eq])
        (ae_of_all _ fun ω => tendsto_ito_increment_dyadic_sup hd B hT U hU_cont k ω)
    · exact ito_increment_dyadic_sup_L2_le hd B hT U hU_ito_L2_diff k m

set_option maxHeartbeats 2000000

/-- **Continuous `L²` Itô integral on `pathFiltration B`** for any `predSigma`-measurable
`Z ∈ L²(dtP P T)`: adapted, integrable, mean `0`, a.s. continuous on `[0, T]` with `M 0 = 0`,
constant after `q` on any `A ∈ ℱ_q` where `Z = 0` on `(q, T] × A`, and a.e.-`t` limit in
probability of `itoRiemannPrime B hd Z t (φ j)` along a subsequence `φ`. -/
theorem exists_contIto_and_riemann_subseq {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    (hB_cont : ∀ ω, Continuous (fun t => MultiBrownian.W B t ω (kitDriver hd)))
    {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → ℝ}
    (hZp : IsPredictableProcess (pathFiltration B).σAlg T Z)
    (hZL2 : MemLp (Function.uncurry Z) 2 (dtP P T)) :
    ∃ M : ℝ → Ω → ℝ,
      (∀ t ∈ Icc 0 T, Measurable[(pathFiltration B).σAlg t] (M t) ∧ Integrable (M t) P) ∧
      (∫ ω, M T ω ∂P = 0) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Icc 0 T) ∧ M 0 ω = 0) ∧
      (∀ (q : ℝ) (hq : q ∈ Icc 0 T) (A : Set Ω),
        MeasurableSet[(pathFiltration B).σAlg q] A →
        (∀ s ∈ Ioc q T, ∀ ω ∈ A, Z s ω = 0) →
        ∀ᵐ ω ∂P, ω ∈ A → M T ω = M q ω) ∧
      (∃ (G : Set ℝ) (φ : ℕ → ℕ),
        StrictMono φ ∧ volume (Ioo 0 T \ G) = 0 ∧
        ∀ t ∈ G ∩ Ioo 0 T,
          TendstoInMeasure P (fun j => itoRiemannPrime B hd Z t (φ j)) atTop (M t)) := by
  have : IsFiniteMeasure (dtP P T) := isFiniteMeasure_dtP
  have : Nonempty {t : ℝ // t ∈ Icc 0 T} := ⟨⟨0, le_rfl, hT.le⟩⟩
  have hW_jm : Measurable (fun p : ℝ × Ω => MultiBrownian.W B p.1 p.2 (kitDriver hd)) :=
    measurable_uncurry_of_continuous_left hB_cont (fun s => MultiBrownian.W_meas B s (kitDriver hd))
  have hchoose : ∀ k : ℕ, ∃ U : JointElem B T,
      ∫ p, (Z p.1 p.2 - U.toFun p.1 p.2) ^ 2 ∂(dtP P T) < (1 / 2 : ℝ) ^ (4 * k) := fun k =>
    exists_jointElem_L2_approx B hT hZp hZL2 (by positivity)
  choose U hU using hchoose
  let M : ℝ → Ω → ℝ := fun t ω => limUnder atTop fun k => (U k).ito hd t ω
  have hU_cont : ∀ k ω, Continuous (fun t => (U k).ito hd t ω) := fun k ω =>
    continuous_finsetSum _ fun j _ => continuous_const.mul
      (((hB_cont ω).comp (continuous_const.min continuous_id)).sub
       ((hB_cont ω).comp (continuous_const.min continuous_id)))
  have hM_meas : ∀ t ∈ Icc 0 T, Measurable[(pathFiltration B).σAlg t] (M t) := fun t ht => by
    have hm : ∀ k, Measurable[(pathFiltration B).σAlg t] ((U k).ito hd t) :=
      fun k => jointElem_ito_meas hd (U k) ht.1 ht.2
    let : MeasurableSpace Ω := (pathFiltration B).σAlg t
    exact (StronglyMeasurable.limUnder fun k => (hm k).stronglyMeasurable).measurable
  have hU_ito_L2_diff : ∀ k₁ k₂, ∀ t ∈ Icc 0 T,
      ∫ ω, ((U k₁).ito hd t ω - (U k₂).ito hd t ω) ^ 2 ∂P ≤
        2 * (1 / 2 : ℝ) ^ (4 * k₁) + 2 * (1 / 2 : ℝ) ^ (4 * k₂) := fun k₁ k₂ t ht => by
    have hrew : ∀ ω, (U k₁).ito hd t ω - (U k₂).ito hd t ω = ((U k₁).add (U k₂).neg).ito hd t ω := fun ω => by
      rw [JointElem.add_ito, JointElem.neg_ito]; ring
    simp_rw [hrew, integral_jointElem_ito_sq hd hT ((U k₁).add (U k₂).neg) ht.1 ht.2]
    have hi1 : Integrable (fun p : ℝ × Ω => (Z p.1 p.2 - (U k₁).toFun p.1 p.2) ^ 2) (dtP P T) :=
      (hZL2.sub (U k₁).memLp_dtP).integrable_sq
    have hi2 : Integrable (fun p : ℝ × Ω => (Z p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2) (dtP P T) :=
      (hZL2.sub (U k₂).memLp_dtP).integrable_sq
    have hcongr : ∀ p : ℝ × Ω, ((U k₁).add (U k₂).neg).toFun p.1 p.2 ^ 2 =
        ((U k₁).toFun p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2 := fun p => by
      rw [JointElem.add_toFun, JointElem.neg_toFun]; ring
    simp_rw [hcongr]
    calc ∫ p in Icc 0 t ×ˢ (Set.univ : Set Ω), ((U k₁).toFun p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2 ∂(dtP P T)
        ≤ ∫ p, ((U k₁).toFun p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2 ∂(dtP P T) :=
          setIntegral_le_integral ((U k₁).memLp_dtP.sub (U k₂).memLp_dtP).integrable_sq (ae_of_all _ fun _ => sq_nonneg _)
      _ ≤ ∫ p, (2 * (Z p.1 p.2 - (U k₁).toFun p.1 p.2) ^ 2 + 2 * (Z p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2) ∂(dtP P T) :=
          integral_mono ((U k₁).memLp_dtP.sub (U k₂).memLp_dtP).integrable_sq ((hi1.const_mul 2).add (hi2.const_mul 2)) fun p => by
            nlinarith [sq_nonneg ((Z p.1 p.2 - (U k₁).toFun p.1 p.2) + (Z p.1 p.2 - (U k₂).toFun p.1 p.2))]
      _ = 2 * ∫ p, (Z p.1 p.2 - (U k₁).toFun p.1 p.2) ^ 2 ∂(dtP P T) +
            2 * ∫ p, (Z p.1 p.2 - (U k₂).toFun p.1 p.2) ^ 2 ∂(dtP P T) := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ 2 * (1 / 2 : ℝ) ^ (4 * k₁) + 2 * (1 / 2 : ℝ) ^ (4 * k₂) := by linarith [hU k₁, hU k₂]
  -- Step 1: Dyadic Doob + Borel–Cantelli ⇒ uniform convergence a.s. on `[0, T]`
  have hsup_meas : ∀ k, Measurable (fun ω => ⨆ t : {t : ℝ // t ∈ Icc 0 T},
      |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) := fun k => measurable_of_Iic fun c => by
    have hck : ∀ ω, Continuous (fun t => |(U (k + 1)).ito hd t ω - (U k).ito hd t ω|) := fun ω =>
      ((hU_cont (k + 1) ω).sub (hU_cont k ω)).abs
    have hset : (fun ω => ⨆ t : {t : ℝ // t ∈ Icc 0 T}, |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ⁻¹' Iic c =
        (⋂ q : ℚ, if hq : (q : ℝ) ∈ Icc 0 T then {ω | |(U (k + 1)).ito hd q ω - (U k).ito hd q ω| ≤ c} else Set.univ) ∩
        {ω | |(U (k + 1)).ito hd T ω - (U k).ito hd T ω| ≤ c} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff, Set.mem_iInter]
      have hbdd : BddAbove (Set.range fun t : {t : ℝ // t ∈ Icc 0 T} => |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) := by
        obtain ⟨t0, _, ht0⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT.le⟩ (hck ω).continuousOn
        exact ⟨|(U (k + 1)).ito hd t0 ω - (U k).ito hd t0 ω|, by rintro _ ⟨t, rfl⟩; exact ht0 t.2⟩
      constructor
      · intro h
        refine ⟨fun q => by split_ifs with hq; exact (le_ciSup hbdd ⟨q, hq⟩).trans h; trivial,
          (le_ciSup hbdd ⟨T, hT.le, le_rfl⟩).trans h⟩
      · rintro ⟨hq, hTle⟩; refine ciSup_le fun ⟨t, ht⟩ => ?_
        rcases ht.2.eq_or_lt with rfl | hlt; · exact hTle
        by_contra hgt; push Not at hgt
        obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp ((hck ω).continuousAt (x := t))
          ((|(U (k + 1)).ito hd t ω - (U k).ito hd t ω| - c) / 2) (by linarith)
        obtain ⟨q, hqt, hqb⟩ := exists_rat_btwn (lt_min hlt (by linarith : t < t + δ))
        have hqI : (q : ℝ) ∈ Icc 0 T := ⟨ht.1.trans hqt.le, (lt_of_lt_of_le hqb (min_le_left _ _)).le⟩
        have hd_lt : dist (q : ℝ) t < δ := by
          rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hqt)]; linarith [lt_of_lt_of_le hqb (min_le_right _ _)]
        have h1 := hball hd_lt; rw [Real.dist_eq, abs_lt] at h1
        have h2 := hq q; rw [dif_pos hqI] at h2
        simp only [Set.mem_setOf_eq] at h2
        linarith [hgt]
    rw [hset]
    exact (MeasurableSet.iInter fun q => by
      split_ifs with hq
      · exact measurableSet_le (((jointElem_ito_meas hd (U (k + 1)) hq.1 hq.2).sub
          (jointElem_ito_meas hd (U k) hq.1 hq.2)).mono ((pathFiltration B).le_ambient q) le_rfl).abs measurable_const
      · exact MeasurableSet.univ).inter
      (measurableSet_le (((jointElem_ito_meas hd (U (k + 1)) hT.le le_rfl).sub
        (jointElem_ito_meas hd (U k) hT.le le_rfl)).mono ((pathFiltration B).le_ambient T) le_rfl).abs measurable_const)
  have hsup : ∀ k : ℕ, ∫⁻ ω, ENNReal.ofReal ((⨆ t : {t : ℝ // t ∈ Icc 0 T},
      |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ^ 2) ∂P ≤
      ENNReal.ofReal (16 * (1 / 2 : ℝ) ^ (4 * k)) := fun k =>
    ito_increment_sup_L2_le hd B hT U hU_cont hU_ito_L2_diff k
  have hbc_unif : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun k t => (U k).ito hd t ω) (fun t => M t ω) atTop (Icc 0 T) := by
    let term : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ENNReal.ofReal (((2 : ℝ) ^ k * ⨆ t : {t : ℝ // t ∈ Icc 0 T},
        |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ^ 2)
    have hterm_meas : ∀ k, Measurable (term k) := fun k =>
      ENNReal.measurable_ofReal.comp ((measurable_const.mul (hsup_meas k)).pow_const 2)
    have hsum_fin : ∫⁻ ω, ∑' k : ℕ, term k ω ∂P ≠ ∞ := by
      rw [lintegral_tsum fun k => (hterm_meas k).aemeasurable]
      have hsumm_g : Summable (fun k : ℕ => 16 * (1 / 4 : ℝ) ^ k) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 16
      refine ne_top_of_le_ne_top hsumm_g.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum fun k => ?_)
      have hrew : ∀ ω, term k ω = ENNReal.ofReal ((4 : ℝ) ^ k) * ENNReal.ofReal ((⨆ t : {t : ℝ // t ∈ Icc 0 T},
            |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) ^ 2) := fun ω => by
        simp only [term]
        rw [← ENNReal.ofReal_mul (by positivity), mul_pow,
          show ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      simp_rw [hrew]
      rw [lintegral_const_mul' (ENNReal.ofReal ((4 : ℝ) ^ k)) _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul' le_rfl (hsup k)).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [mul_left_comm (4 ^ k)]
      refine congr_arg (fun x => (16 : ℝ) * x) ?_
      rw [pow_mul, show ((1 / 2 : ℝ) ^ 4) = (1 / 16) by norm_num, ← mul_pow]
      norm_num
    have hsumm : ∀ᵐ ω ∂P, Summable (fun k : ℕ => ⨆ t : {t : ℝ // t ∈ Icc 0 T},
        |(U (k + 1)).ito hd t.1 ω - (U k).ito hd t.1 ω|) := by
      filter_upwards [ae_lt_top (Measurable.tsum hterm_meas) hsum_fin] with ω hω
      obtain ⟨N0, hN0⟩ := (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne)) 1 zero_lt_one
      rw [← summable_nat_add_iff N0]
      refine Summable.of_nonneg_of_le (fun _ => Real.iSup_nonneg fun _ => abs_nonneg _) (fun k => ?_)
        (summable_geometric_two.comp_injective (add_left_injective N0))
      have hk : term (k + N0) ω ≤ 1 := hN0 (k + N0) (Nat.le_add_left N0 k)
      have h1 : ((2 : ℝ) ^ (k + N0) * (⨆ t : {t : ℝ // t ∈ Icc 0 T},
          |(U (k + N0 + 1)).ito hd t.1 ω - (U (k + N0)).ito hd t.1 ω|)) ^ 2 ≤ 1 := ENNReal.ofReal_le_one.mp hk
      have hnn : 0 ≤ (2 : ℝ) ^ (k + N0) * (⨆ t : {t : ℝ // t ∈ Icc 0 T},
          |(U (k + N0 + 1)).ito hd t.1 ω - (U (k + N0)).ito hd t.1 ω|) :=
        mul_nonneg (by positivity) (Real.iSup_nonneg fun _ => abs_nonneg _)
      change (⨆ t : {t : ℝ // t ∈ Icc 0 T}, |(U (k + N0 + 1)).ito hd t.1 ω - (U (k + N0)).ito hd t.1 ω|) ≤ (1 / 2 : ℝ) ^ (k + N0)
      have hmul : (2 : ℝ) ^ (k + N0) * (⨆ t : {t : ℝ // t ∈ Icc 0 T},
          |(U (k + N0 + 1)).ito hd t.1 ω - (U (k + N0)).ito hd t.1 ω|) ≤ 1 := by
        nlinarith [h1, hnn]
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + N0) := by positivity
      have hprod : (2 : ℝ) ^ (k + N0) * (1 / 2 : ℝ) ^ (k + N0) = 1 := by
        rw [← mul_pow]; norm_num
      exact (mul_le_mul_iff_of_pos_left hpow).mp (by linarith [hmul, hprod])
    filter_upwards [hsumm] with ω hω
    have hcauchy : UniformCauchySeqOn (fun k t => (U k).ito hd t ω) atTop (Icc 0 T) := by
      rw [Metric.uniformCauchySeqOn_iff]; intro ε hε
      obtain ⟨K, hK⟩ := (Metric.cauchySeq_iff.mp hω.hasSum.tendsto_sum_nat.cauchySeq) ε hε
      refine ⟨K, fun m hm n hn t ht => ?_⟩
      wlog hmn : m ≤ n generalizing m n
      · rw [dist_comm]; exact this n hn m hm (le_of_not_ge hmn)
      rw [Real.dist_eq, show (U m).ito hd t ω - (U n).ito hd t ω = -((U n).ito hd t ω - (U m).ito hd t ω) by ring, abs_neg]
      have htel : (U n).ito hd t ω - (U m).ito hd t ω =
          ∑ k ∈ Finset.Ico m n, ((U (k + 1)).ito hd t ω - (U k).ito hd t ω) := by
        clear hK hm hn; induction hmn with
        | refl => simp
        | @step r hr ih => rw [Finset.sum_Ico_succ_top hr, ← ih]; ring
      rw [htel]
      calc |∑ k ∈ Finset.Ico m n, ((U (k + 1)).ito hd t ω - (U k).ito hd t ω)|
          ≤ ∑ k ∈ Finset.Ico m n, |(U (k + 1)).ito hd t ω - (U k).ito hd t ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.Ico m n, ⨆ s : {s : ℝ // s ∈ Icc 0 T}, |(U (k + 1)).ito hd s.1 ω - (U k).ito hd s.1 ω| :=
            Finset.sum_le_sum fun k _ => by
              obtain ⟨t0, _, ht0⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT.le⟩ (((hU_cont (k + 1) ω).sub (hU_cont k ω)).abs.continuousOn)
              exact le_ciSup (f := fun s : {s : ℝ // s ∈ Icc 0 T} =>
                  |(U (k + 1)).ito hd s.1 ω - (U k).ito hd s.1 ω|)
                ⟨|(U (k + 1)).ito hd t0 ω - (U k).ito hd t0 ω|,
                  fun _ ⟨s, hs⟩ => hs ▸ ht0 s.property⟩ ⟨t, ht⟩
        _ < ε := by
            have h := hK n hn m hm
            rw [Real.dist_eq, ← Finset.sum_Ico_eq_sub _ hmn,
              abs_of_nonneg (Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _)] at h
            exact h
    exact hcauchy.tendstoUniformlyOn_of_tendsto fun t ht =>
      tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy.cauchySeq ht))
  -- Step 2: Fatou gives `M t ∈ L²` and `∫ (M t - (U k).ito t)² ≤ 4 * 2^(-4k)` for all `t ∈ [0, T]`
  have hM_L2 : ∀ t ∈ Icc 0 T, MemLp (M t) 2 P ∧
      ∀ k, ∫ ω, (M t ω - (U k).ito hd t ω) ^ 2 ∂P ≤ 4 * (1 / 2 : ℝ) ^ (4 * k) := fun t ht => by
    have hae_t : ∀ᵐ ω ∂P, Tendsto (fun j => (U j).ito hd t ω) atTop (𝓝 (M t ω)) :=
      hbc_unif.mono fun ω hω => hω.tendsto_at ht
    have hbd : ∀ k, Integrable (fun ω => (M t ω - (U k).ito hd t ω) ^ 2) P ∧
        ∫ ω, (M t ω - (U k).ito hd t ω) ^ 2 ∂P ≤ 4 * (1 / 2 : ℝ) ^ (4 * k) := fun k => by
      have hfat : ∫⁻ ω, ENNReal.ofReal ((M t ω - (U k).ito hd t ω) ^ 2) ∂P ≤
          ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ (4 * k)) := by
        calc ∫⁻ ω, ENNReal.ofReal ((M t ω - (U k).ito hd t ω) ^ 2) ∂P
            = ∫⁻ ω, liminf (fun j => ENNReal.ofReal (((U j).ito hd t ω - (U k).ito hd t ω) ^ 2)) atTop ∂P :=
              lintegral_congr_ae (hae_t.mono fun ω hω =>
                (ENNReal.tendsto_ofReal ((hω.sub tendsto_const_nhds).pow 2)).liminf_eq.symm)
          _ ≤ liminf (fun j => ∫⁻ ω, ENNReal.ofReal (((U j).ito hd t ω - (U k).ito hd t ω) ^ 2) ∂P) atTop :=
              lintegral_liminf_le' fun j => (ENNReal.measurable_ofReal.comp
                ((((jointElem_ito_meas hd (U j) ht.1 ht.2).sub (jointElem_ito_meas hd (U k) ht.1 ht.2)).mono
                  ((pathFiltration B).le_ambient t) le_rfl).pow_const 2)).aemeasurable
          _ ≤ liminf (fun j => ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (4 * k) + 2 * (1 / 2 : ℝ) ^ (4 * j))) atTop := by
              refine liminf_le_liminf (Eventually.of_forall fun j => ?_) (by isBoundedDefault) (by isBoundedDefault)
              have hi : Integrable (fun ω => ((U j).ito hd t ω - (U k).ito hd t ω) ^ 2) P :=
                ((jointElem_ito_memLp hd (U j) ht.1).sub (jointElem_ito_memLp hd (U k) ht.1)).integrable_sq
              rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [show (fun ω => ((U j).ito hd t ω - (U k).ito hd t ω) ^ 2) =
                fun ω => ((U k).ito hd t ω - (U j).ito hd t ω) ^ 2 from funext fun _ => by ring]
              exact hU_ito_L2_diff k j t ht
          _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (4 * k)) := by
              have h0 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (4 * j)) atTop (𝓝 0) := by
                have : (fun j : ℕ => (1 / 2 : ℝ) ^ (4 * j)) = fun j => (1 / 16 : ℝ) ^ j :=
                  funext fun j => by rw [pow_mul]; norm_num
                rw [this]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
              exact (ENNReal.tendsto_ofReal (by simpa using tendsto_const_nhds.add (h0.const_mul 2))).liminf_eq
          _ ≤ ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ (4 * k)) :=
              ENNReal.ofReal_le_ofReal (by linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (4 * k) by positivity])
      have hint : Integrable (fun ω => (M t ω - (U k).ito hd t ω) ^ 2) P := by
        refine ⟨((((hM_meas t ht).sub (jointElem_ito_meas hd (U k) ht.1 ht.2)).mono
          ((pathFiltration B).le_ambient t) le_rfl).pow_const 2).aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        have heq : ∫⁻ ω, ‖(M t ω - (U k).ito hd t ω) ^ 2‖ₑ ∂P =
            ∫⁻ ω, ENNReal.ofReal ((M t ω - (U k).ito hd t ω) ^ 2) ∂P :=
          lintegral_congr fun ω => Real.enorm_eq_ofReal (sq_nonneg _)
        rw [heq]; exact hfat.trans_lt ENNReal.ofReal_lt_top
      refine ⟨hint, ?_⟩
      rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
        ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
      exact hfat
    have hdiff0 : MemLp (fun ω => M t ω - (U 0).ito hd t ω) 2 P :=
      memLp_two_iff_integrable_sq ((((hM_meas t ht).sub (jointElem_ito_meas hd (U 0) ht.1 ht.2)).mono
        ((pathFiltration B).le_ambient t) le_rfl).aestronglyMeasurable) |>.mpr (hbd 0).1
    have hsum0 := hdiff0.add (jointElem_ito_memLp hd (U 0) ht.1)
    have hsum_eq : (fun ω => M t ω - (U 0).ito hd t ω) + (U 0).ito hd t = M t :=
      funext fun ω => sub_add_cancel _ _
    rw [hsum_eq] at hsum0
    exact ⟨hsum0, fun k => (hbd k).2⟩
  -- Step 3: Assemble all 5 conclusions (with `M` as the existential witness!)
  refine ⟨M, fun t ht => ⟨hM_meas t ht, (hM_L2 t ht).1.integrable one_le_two⟩, ?_, ?_, ?_, ?_⟩
  · -- Clause 2: `∫ M T = 0`
    have h0 : ∀ k, ∫ ω, (U k).ito hd T ω ∂P = 0 := fun k => by
      have h := setIntegral_jointElem_ito hd (U k) le_rfl hT.le le_rfl MeasurableSet.univ
      have h0' : (U k).ito hd 0 = fun _ => 0 := funext fun ω => Finset.sum_eq_zero fun j _ => by
        rw [min_eq_right ((U k).hab j).1, min_eq_right (((U k).hab j).1.trans ((U k).hab j).2.1), sub_self, mul_zero]
      simpa [h0'] using h
    refine eq_of_forall_dist_le fun ε hε => ?_
    have hlim : Tendsto (fun k : ℕ => Real.sqrt (4 * (1 / 2 : ℝ) ^ (4 * k))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (4 * k)) atTop (𝓝 0) := by
        have : (fun k : ℕ => (1 / 2 : ℝ) ^ (4 * k)) = fun k => (1 / 16 : ℝ) ^ k := funext fun k => by rw [pow_mul]; norm_num
        rw [this]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h4 : Tendsto (fun k : ℕ => 4 * (1 / 2 : ℝ) ^ (4 * k)) atTop (𝓝 0) := by
        simpa using h1.const_mul 4
      have hcomp := (Real.continuous_sqrt.tendsto 0).comp h4
      have hfun : (fun k : ℕ => Real.sqrt (4 * (1 / 2 : ℝ) ^ (4 * k))) =
          (Real.sqrt ∘ fun k : ℕ => 4 * (1 / 2 : ℝ) ^ (4 * k)) := rfl
      rw [hfun]
      convert hcomp
      exact Real.sqrt_zero.symm
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
    have hk' : Real.sqrt (4 * (1 / 2 : ℝ) ^ (4 * k)) ≤ ε := by
      have := hk k le_rfl; rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at this; exact this.le
    rw [Real.dist_eq, sub_zero, ← sub_zero (∫ ω, M T ω ∂P), ← h0 k,
      ← integral_sub ((hM_L2 T ⟨hT.le, le_rfl⟩).1.integrable one_le_two)
        ((jointElem_ito_memLp hd (U k) hT.le).integrable one_le_two)]
    calc |∫ ω, (M T ω - (U k).ito hd T ω) ∂P|
        ≤ ∫ ω, |M T ω - (U k).ito hd T ω| ∂P := abs_integral_le_integral_abs
      _ ≤ Real.sqrt (∫ ω, (M T ω - (U k).ito hd T ω) ^ 2 ∂P) :=
          integral_abs_le_sqrt_integral_sq ((hM_L2 T ⟨hT.le, le_rfl⟩).1.sub (jointElem_ito_memLp hd (U k) hT.le))
      _ ≤ Real.sqrt (4 * (1 / 2 : ℝ) ^ (4 * k)) := Real.sqrt_le_sqrt ((hM_L2 T ⟨hT.le, le_rfl⟩).2 k)
      _ ≤ ε := hk'
  · -- Clause 3: Continuity and `M 0 = 0` a.s.
    filter_upwards [hbc_unif] with ω hω
    refine ⟨hω.continuousOn (Frequently.of_forall fun k =>
        (hU_cont k ω).continuousOn (s := Icc 0 T)), ?_⟩
    have h0 : ∀ k, (U k).ito hd 0 ω = 0 := fun k => Finset.sum_eq_zero fun j _ => by
      rw [min_eq_right ((U k).hab j).1, min_eq_right (((U k).hab j).1.trans ((U k).hab j).2.1), sub_self, mul_zero]
    simp [M, h0, tendsto_const_nhds.limUnder_eq]
  · -- Clause 4: `Z = 0` on `(q, T] × A` (`A ∈ ℱ_q`) ⇒ `M T = M q` a.s. on `A`
    intro q hq A hA hZ0
    have hzero_int : ∫ ω in A, (M T ω - M q ω) ^ 2 ∂P = 0 := by
      refine le_antisymm ?_ (setIntegral_nonneg ((pathFiltration B).le_ambient q A hA) fun _ _ => sq_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have h1 : Tendsto (fun k : ℕ => 27 * (1 / 2 : ℝ) ^ (4 * k)) atTop (𝓝 0) := by
        have hpow : (fun k : ℕ => 27 * (1 / 2 : ℝ) ^ (4 * k)) = fun k => 27 * (1 / 16 : ℝ) ^ k :=
          funext fun k => by rw [pow_mul]; norm_num
        rw [hpow]
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
          (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num)).const_mul (27 : ℝ)
      obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp h1) ε hε
      have hk' : 27 * (1 / 2 : ℝ) ^ (4 * k) ≤ ε := by
        have := hk k le_rfl; rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this.le
      let Uk_tail : JointElem B T :=
        { n := (U k).n
          a := fun j => max ((U k).a j) q
          b := fun j => max ((U k).b j) q
          h := fun j => A.indicator ((U k).h j)
          hab := fun j => ⟨le_max_of_le_right hq.1, max_le_max_right q ((U k).hab j).2.1, max_le ((U k).hab j).2.2 hq.2⟩
          h_meas := fun j => (((U k).h_meas j).mono ((pathFiltration B).mono (le_max_left _ _)) le_rfl).indicator
            ((pathFiltration B).mono (le_max_right _ _) A hA)
          h_bdd := fun j => let ⟨C, hC⟩ := (U k).h_bdd j; ⟨max C 0, fun ω => by
            by_cases hω : ω ∈ A
            · rw [Set.indicator_of_mem hω]; exact (hC ω).trans (le_max_left _ _)
            · rw [Set.indicator_of_notMem hω, abs_zero]; exact le_max_right _ _⟩ }
      have htail_ito : ∀ ω, Uk_tail.ito hd T ω = A.indicator (fun ω => (U k).ito hd T ω - (U k).ito hd q ω) ω := fun ω => by
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω]; unfold JointElem.ito; dsimp only [Uk_tail]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Set.indicator_of_mem hω, min_eq_left (max_le ((U k).hab j).2.2 hq.2),
            min_eq_left (max_le (((U k).hab j).2.1.trans ((U k).hab j).2.2) hq.2),
            min_eq_left ((U k).hab j).2.2, min_eq_left (((U k).hab j).2.1.trans ((U k).hab j).2.2)]
          rcases le_total ((U k).a j) q with ha | ha <;> rcases le_total ((U k).b j) q with hb | hb
          · rw [max_eq_right ha, max_eq_right hb, min_eq_left ha, min_eq_left hb]; ring
          · rw [max_eq_right ha, max_eq_left hb, min_eq_left ha, min_eq_right hb]; ring
          · have ha_eq : (U k).a j = q := le_antisymm (((U k).hab j).2.1.trans hb) ha
            have hb_eq : (U k).b j = q := le_antisymm hb (ha.trans ((U k).hab j).2.1)
            simp [ha_eq, hb_eq]
          · rw [max_eq_left ha, max_eq_left hb, min_eq_right ha, min_eq_right hb]; ring
        · rw [Set.indicator_of_notMem hω]; exact Finset.sum_eq_zero fun j _ => by simp [Uk_tail, hω]
      have htail_sq : ∫ ω in A, ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2 ∂P ≤ (1 / 2 : ℝ) ^ (4 * k) := by
        have h1' : ∫ ω in A, ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2 ∂P = ∫ ω, Uk_tail.ito hd T ω ^ 2 ∂P := by
          rw [← integral_indicator ((pathFiltration B).le_ambient q A hA)]
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          change A.indicator (fun ω => ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2) ω =
            Uk_tail.ito hd T ω ^ 2
          by_cases hω : ω ∈ A
          · rw [Set.indicator_of_mem hω, htail_ito ω, Set.indicator_of_mem hω]
          · rw [Set.indicator_of_notMem hω, htail_ito ω, Set.indicator_of_notMem hω, sq, mul_zero]
        rw [h1', integral_jointElem_ito_sq hd hT Uk_tail hT.le le_rfl]
        have hle_Z : ∀ p : ℝ × Ω, p ∈ Icc 0 T ×ˢ (Set.univ : Set Ω) →
            Uk_tail.toFun p.1 p.2 ^ 2 ≤ (Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2 := fun p hp => by
          by_cases hcond : q < p.1 ∧ p.2 ∈ A
          · have hUk_eq : Uk_tail.toFun p.1 p.2 = (U k).toFun p.1 p.2 := by
              unfold JointElem.toFun Uk_tail; refine Finset.sum_congr rfl fun j _ => ?_
              have hiff : (max ((U k).a j) q < p.1 ∧ p.1 ≤ max ((U k).b j) q) ↔ ((U k).a j < p.1 ∧ p.1 ≤ (U k).b j) := by
                constructor
                · rintro ⟨h1, h2⟩; refine ⟨lt_of_le_of_lt (le_max_left _ _) h1, ?_⟩
                  rcases le_total ((U k).b j) q with hb | hb
                  · linarith [max_eq_right hb ▸ h2]
                  · rwa [max_eq_left hb] at h2
                · rintro ⟨h1, h2⟩; exact ⟨max_lt h1 hcond.1, h2.trans (le_max_left _ _)⟩
              by_cases h : (U k).a j < p.1 ∧ p.1 ≤ (U k).b j
              · have h' := hiff.mpr h
                simp [h, h', hcond.2, Set.indicator_of_mem]
              · have h' : ¬ (max ((U k).a j) q < p.1 ∧ p.1 ≤ max ((U k).b j) q) := fun hh => h (hiff.mp hh)
                split_ifs with hif
                · exact (h' hif).elim
                · rfl
            rw [hUk_eq, hZ0 p.1 ⟨hcond.1, hp.1.2⟩ p.2 hcond.2, zero_sub, neg_sq]
          · have hUk_0 : Uk_tail.toFun p.1 p.2 = 0 := Finset.sum_eq_zero fun j _ => by
              by_cases h1 : max ((U k).a j) q < p.1 ∧ p.1 ≤ max ((U k).b j) q
              · have hnotA : p.2 ∉ A := fun hA' => hcond ⟨lt_of_le_of_lt (le_max_right _ _) h1.1, hA'⟩
                simp [Uk_tail, h1, hnotA, Set.indicator_of_notMem]
              · split_ifs with hif
                · exact (h1 hif).elim
                · rfl
            rw [hUk_0, zero_pow two_ne_zero]; exact sq_nonneg _
        calc ∫ p in Icc 0 T ×ˢ (Set.univ : Set Ω), Uk_tail.toFun p.1 p.2 ^ 2 ∂(dtP P T)
            ≤ ∫ p in Icc 0 T ×ˢ (Set.univ : Set Ω), (Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2 ∂(dtP P T) :=
              setIntegral_mono_on Uk_tail.memLp_dtP.integrable_sq.integrableOn
                (hZL2.sub (U k).memLp_dtP).integrable_sq.integrableOn (measurableSet_Icc.prod MeasurableSet.univ) hle_Z
          _ ≤ ∫ p, (Z p.1 p.2 - (U k).toFun p.1 p.2) ^ 2 ∂(dtP P T) :=
              setIntegral_le_integral (hZL2.sub (U k).memLp_dtP).integrable_sq (ae_of_all _ fun _ => sq_nonneg _)
          _ ≤ (1 / 2 : ℝ) ^ (4 * k) := (hU k).le
      have hi1 : Integrable (fun ω => (M T ω - (U k).ito hd T ω) ^ 2) P :=
        ((hM_L2 T ⟨hT.le, le_rfl⟩).1.sub (jointElem_ito_memLp hd (U k) hT.le)).integrable_sq
      have hi2 : Integrable (fun ω => (M q ω - (U k).ito hd q ω) ^ 2) P :=
        ((hM_L2 q hq).1.sub (jointElem_ito_memLp hd (U k) hq.1)).integrable_sq
      have hi3 : Integrable (fun ω => ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2) P :=
        ((jointElem_ito_memLp hd (U k) hT.le).sub (jointElem_ito_memLp hd (U k) hq.1)).integrable_sq
      calc ∫ ω in A, (M T ω - M q ω) ^ 2 ∂P
          ≤ ∫ ω in A, (3 * (M T ω - (U k).ito hd T ω) ^ 2 +
              3 * ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2 + 3 * (M q ω - (U k).ito hd q ω) ^ 2) ∂P :=
            setIntegral_mono_on ((hM_L2 T ⟨hT.le, le_rfl⟩).1.sub (hM_L2 q hq).1).integrable_sq.integrableOn
              (((hi1.const_mul 3).add (hi3.const_mul 3)).add (hi2.const_mul 3)).integrableOn
              ((pathFiltration B).le_ambient q A hA) fun ω _ => by
                nlinarith [sq_nonneg ((M T ω - (U k).ito hd T ω) - ((U k).ito hd T ω - (U k).ito hd q ω)),
                  sq_nonneg ((M T ω - (U k).ito hd T ω) + (M q ω - (U k).ito hd q ω)),
                  sq_nonneg (((U k).ito hd T ω - (U k).ito hd q ω) + (M q ω - (U k).ito hd q ω))]
        _ ≤ 3 * ∫ ω, (M T ω - (U k).ito hd T ω) ^ 2 ∂P + 3 * ∫ ω in A, ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2 ∂P +
              3 * ∫ ω, (M q ω - (U k).ito hd q ω) ^ 2 ∂P := by
            have I1 : Integrable (fun ω => 3 * (M T ω - (U k).ito hd T ω) ^ 2) (P.restrict A) :=
              (hi1.const_mul 3).restrict
            have I3 : Integrable (fun ω => 3 * ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2) (P.restrict A) :=
              (hi3.const_mul 3).restrict
            have I2 : Integrable (fun ω => 3 * (M q ω - (U k).ito hd q ω) ^ 2) (P.restrict A) :=
              (hi2.const_mul 3).restrict
            have I13 : Integrable (fun ω =>
                3 * (M T ω - (U k).ito hd T ω) ^ 2 +
                3 * ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2) (P.restrict A) := I1.add I3
            rw [integral_add (μ := P.restrict A)
                  (f := fun ω =>
                    3 * (M T ω - (U k).ito hd T ω) ^ 2 +
                    3 * ((U k).ito hd T ω - (U k).ito hd q ω) ^ 2) I13 I2,
                integral_add (μ := P.restrict A)
                  (f := fun ω => 3 * (M T ω - (U k).ito hd T ω) ^ 2) I1 I3,
                integral_const_mul, integral_const_mul, integral_const_mul]
            have hle1 := setIntegral_le_integral (s := A) hi1 (ae_of_all _ fun _ => sq_nonneg _)
            have hle2 := setIntegral_le_integral (s := A) hi2 (ae_of_all _ fun _ => sq_nonneg _)
            refine add_le_add (add_le_add ?_ le_rfl) ?_
            · exact mul_le_mul_of_nonneg_left hle1 (by norm_num)
            · exact mul_le_mul_of_nonneg_left hle2 (by norm_num)
        _ ≤ 27 * (1 / 2 : ℝ) ^ (4 * k) := by linarith [(hM_L2 T ⟨hT.le, le_rfl⟩).2 k, htail_sq, (hM_L2 q hq).2 k]
        _ ≤ 0 + ε := by linarith
    have hae0 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      ((hM_L2 T ⟨hT.le, le_rfl⟩).1.sub (hM_L2 q hq).1).integrable_sq.integrableOn).mp hzero_int
    have hae0' : ∀ᵐ ω ∂P, ω ∈ A → (M T ω - M q ω) ^ 2 = 0 := by
      have h : ∀ᵐ ω ∂P.restrict A, (M T ω - M q ω) ^ 2 = 0 := by
        filter_upwards [hae0] with ω hω
        simpa [Pi.zero_apply, Pi.sub_apply] using hω
      rw [ae_restrict_iff' ((pathFiltration B).le_ambient q A hA)] at h
      exact h
    filter_upwards [hae0'] with ω hω hωA
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hω hωA))
  · -- Clause 5
    exact exists_riemann_subseq_from_contIto hd B hT hZp hW_jm hZL2 U hU M
      (fun _ _ => rfl) hM_meas hM_L2

end SignatureVolatility
