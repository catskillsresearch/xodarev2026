module

public import SignatureVolatility.ItoCalculusKit.FrozenIncrement8

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Orthogonality of the frozen-integrand error

`A_{u,v} = I_v - I_u - H_u (W_v - W_u)` satisfies `E[g · A_{u,v}] = 0` for every `𝓕_u`-measurable
`g` with `g · A_{u,v}` integrable (`integral_mul_frozenIncr_eq_zero`), so adapted transforms
`∑ cᵢ A_{τᵢ,τᵢ₊₁}` obey the discrete `L⁴` martingale bound
(`integral_sum_mul_frozenIncr_pow_four_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The frozen-integrand error `I_v - I_u - H_u ΔW` of the raw Itô limit. -/
noncomputable def frozenIncr (B : MultiBrownian Ω P d) (hd : 0 < d) (H : ℝ → Ω → ℝ) (u v : ℝ)
    (ω : Ω) : ℝ :=
  kitItoIntRaw B H v ω - kitItoIntRaw B H u ω - H u ω * wnnIncr B (kitDriver hd) u v ω

lemma abs_clamp_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) :
    |max (-K) (min K x)| ≤ |x| ∧ |max (-K) (min K x)| ≤ K := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  refine ⟨abs_le.mpr ⟨le_max_of_le_right (le_min (by linarith) h1),
    max_le (by linarith) (min_le_of_right_le h2)⟩,
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩

lemma abs_pow_three_mul_le (a b : ℝ) : |a ^ 3 * b| ≤ a ^ 4 + b ^ 4 := by
  rw [abs_mul, abs_pow]
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have ea : a ^ 4 = |a| ^ 4 := (Even.pow_abs (by decide) a).symm
  have eb : b ^ 4 = |b| ^ 4 := (Even.pow_abs (by decide) b).symm
  rw [ea, eb]
  rcases le_total |b| |a| with h | h
  · have : |a| ^ 3 * |b| ≤ |a| ^ 3 * |a| := mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [pow_nonneg hb 4]
  · have h3 : |a| ^ 3 ≤ |b| ^ 3 := pow_le_pow_left₀ ha h 3
    have : |a| ^ 3 * |b| ≤ |b| ^ 3 * |b| := mul_le_mul_of_nonneg_right h3 hb
    nlinarith [pow_nonneg ha 4]

lemma memLp_pow_four_two {f : Ω → ℝ} (hf : MemLp f 8 P) : MemLp (fun ω => f ω ^ 4) 2 P := by
  refine (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.pow 4)).mpr ?_
  exact (integrable_pow_of_memLp_eight hf (k := 8) le_rfl).congr
    (ae_of_all _ fun ω => by simp only [Pi.pow_apply]; ring)

section FrozenOrth

variable (B : MultiBrownian Ω P d) (hd : 0 < d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- **The frozen-integrand error is orthogonal to the past.** -/
theorem integral_mul_frozenIncr_eq_zero (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {g : Ω → ℝ} (hg : Measurable[(pathFiltration B).σAlg u] g)
    (hgA : Integrable (fun ω => g ω * frozenIncr B hd H u v ω) P) :
    ∫ ω, g ω * frozenIncr B hd H u v ω ∂P = 0 := by
  set k := kitDriver hd
  have hv : 0 ≤ v := hu.trans huv
  have hIv := (kitItoIntRaw_of_holderAdapted B hd hv (hH.mono hvt)).2.1
  have hIu := (kitItoIntRaw_of_holderAdapted B hd hu (hH.mono (huv.trans hvt))).2.1
  have hHu := hH.meas u hu (huv.trans hvt)
  have hHW := memLp_mul_wnnIncr B k hu huv hHu (hH.memLp u hu (huv.trans hvt))
  have hAm : AEStronglyMeasurable (frozenIncr B hd H u v) P :=
    ((hIv.sub hIu).sub hHW).aestronglyMeasurable
  set gK : ℕ → Ω → ℝ := fun K ω => max (-(K : ℝ)) (min (K : ℝ) (g ω)) with hgK
  have hgKm : ∀ K, Measurable[(pathFiltration B).σAlg u] (gK K) := fun K =>
    measurable_const.max (measurable_const.min hg)
  have hgKa : ∀ K, Measurable (gK K) := fun K =>
    (hgKm K).mono ((pathFiltration B).le_ambient _) le_rfl
  have hgK2 : ∀ K, MemLp (gK K) 2 P := fun K =>
    MemLp.of_bound (hgKa K).aestronglyMeasurable (K : ℝ) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact (abs_clamp_le (Nat.cast_nonneg K) (g ω)).2)
  have hzero : ∀ K, ∫ ω, gK K ω * frozenIncr B hd H u v ω ∂P = 0 := by
    intro K
    have h1 := integral_mul_kitItoIntRaw_sub_eq_zero B hd hH hu huv hvt (hgKm K) (hgK2 K)
    have hgm : Measurable[(pathFiltration B).σAlg u] (fun ω => gK K ω * H u ω) :=
      (hgKm K).mul hHu
    have h2 := (indepFun_pathFiltration_wnnIncr B k huv hgm).integral_fun_mul_eq_mul_integral
      (hgm.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
      (measurable_wnnIncr B k _ _).aestronglyMeasurable
    have hmean := (hasLaw_wnnIncr B k hu huv).integral_eq
    rw [integral_id_gaussianReal] at hmean
    rw [hmean, mul_zero] at h2
    have i1 : Integrable (fun ω => gK K ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω)) P :=
      integrable_mul_of_memLp_two (hgK2 K) ((hIv.sub hIu).mono_exponent (by norm_num))
    have i2 : Integrable (fun ω => gK K ω * (H u ω * wnnIncr B k u v ω)) P :=
      integrable_mul_of_memLp_two (hgK2 K) (hHW.mono_exponent (by norm_num))
    have h3 : ∫ ω, gK K ω * (H u ω * wnnIncr B k u v ω) ∂P = 0 := by
      rw [← h2]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only; ring
    calc ∫ ω, gK K ω * frozenIncr B hd H u v ω ∂P
        = ∫ ω, (gK K ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) -
            gK K ω * (H u ω * wnnIncr B k u v ω)) ∂P := by
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [frozenIncr, k]; ring
      _ = 0 := by rw [integral_sub i1 i2, h1, h3, sub_zero]
  have hlim : Tendsto (fun K : ℕ => ∫ ω, gK K ω * frozenIncr B hd H u v ω ∂P) atTop
      (𝓝 (∫ ω, g ω * frozenIncr B hd H u v ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖g ω * frozenIncr B hd H u v ω‖)
      (fun K => (hgKa K).aestronglyMeasurable.mul hAm) hgA.norm
      (fun K => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_clamp_le (Nat.cast_nonneg K) (g ω)).1
        (abs_nonneg _)
    · refine Tendsto.mul_const _ (tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_ge_atTop ⌈|g ω|⌉₊] with K hK
      have hK' : |g ω| ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hK)
      have ha := abs_le.mp hK'
      simp only [hgK]
      rw [min_eq_right ha.2, max_eq_right ha.1]
  have hconst : Tendsto (fun K : ℕ => ∫ ω, gK K ω * frozenIncr B hd H u v ω ∂P) atTop (𝓝 0) := by
    simp_rw [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

/-- Adaptedness of the frozen-integrand error. -/
lemma measurable_frozenIncr (hH : HolderAdapted B H t K) {u v s : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvs : v ≤ s) (hvt : v ≤ t) :
    Measurable[(pathFiltration B).σAlg s] (frozenIncr B hd H u v) := by
  have hv : 0 ≤ v := hu.trans huv
  have hIv := measurable_kitItoIntRaw_path B H hv fun r hr0 hr =>
    (hH.meas r hr0 (hr.trans hvt)).mono ((pathFiltration B).mono hr) le_rfl
  have hIu := measurable_kitItoIntRaw_path B H hu fun r hr0 hr =>
    (hH.meas r hr0 (hr.trans (huv.trans hvt))).mono ((pathFiltration B).mono hr) le_rfl
  exact ((hIv.mono ((pathFiltration B).mono hvs) le_rfl).sub
    (hIu.mono ((pathFiltration B).mono (huv.trans hvs)) le_rfl)).sub
    (((hH.meas u hu (huv.trans hvt)).mono ((pathFiltration B).mono (huv.trans hvs)) le_rfl).mul
      (measurable_wnnIncr_pathFiltration B (kitDriver hd) hu hv (huv.trans hvs) hvs))

/-- **`L⁴` bound for adapted transforms of the frozen-integrand errors.** -/
theorem integral_sum_mul_frozenIncr_pow_four_le (hH : HolderAdapted8 B H t K) {τ : ℕ → ℝ}
    (hτ0 : 0 ≤ τ 0) (hτ : Monotone τ) (m : ℕ) (hτm : τ m ≤ t) {c : ℕ → Ω → ℝ}
    (hcm : ∀ i < m, Measurable[(pathFiltration B).σAlg (τ i)] (c i))
    (hc8 : ∀ i < m, MemLp (c i) 8 P) {Cc : ℝ} (hCc : ∀ i < m, ∫ ω, c i ω ^ 8 ∂P ≤ Cc) :
    ∫ ω, (∑ i ∈ range m, c i ω * frozenIncr B hd H (τ i) (τ (i + 1)) ω) ^ 4 ∂P ≤
      16 * (root4 Cc * root4 (128 * 14 ^ 4 * gauss8Const * K) *
        ∑ i ∈ range m, (τ (i + 1) - τ i) ^ 2) ^ 2 := by
  have hτn : ∀ i, 0 ≤ τ i := fun i => hτ0.trans (hτ (Nat.zero_le i))
  have hstep : ∀ i, τ i ≤ τ (i + 1) := fun i => hτ (Nat.le_succ i)
  have hle : ∀ i < m, τ (i + 1) ≤ t := fun i hi => (hτ (Nat.succ_le_of_lt hi)).trans hτm
  have hH4 := hH.toHolderAdapted
  set CA : ℝ := 128 * 14 ^ 4 * gauss8Const * K with hCA
  have hCA0 : 0 ≤ CA := by have := hH.K_nonneg; have := gauss8Const_nonneg; positivity
  set A : ℕ → Ω → ℝ := fun i => frozenIncr B hd H (τ i) (τ (i + 1)) with hAdef
  have hAm : ∀ i < m, ∀ s, τ (i + 1) ≤ s →
      Measurable[(pathFiltration B).σAlg s] (A i) := fun i hi s hs =>
    measurable_frozenIncr B hd hH4 (hτn i) (hstep i) hs (hle i hi)
  have hAa : ∀ i < m, Measurable (A i) := fun i hi =>
    (hAm i hi _ le_rfl).mono ((pathFiltration B).le_ambient _) le_rfl
  have hA8 : ∀ i < m, Integrable (fun ω => A i ω ^ 8) P ∧
      ∫ ω, A i ω ^ 8 ∂P ≤ CA * (τ (i + 1) - τ i) ^ 8 := fun i hi =>
    integral_kitItoIntRaw_sub_frozen_pow_eight_le B hd hH (hτn i) (hstep i) (hle i hi)
  have hAL : ∀ i < m, MemLp (A i) 8 P := fun i hi =>
    memLp_eight_of_integrable_pow_eight (hAa i hi).aestronglyMeasurable (hA8 i hi).1
  set ξ : ℕ → Ω → ℝ := fun i ω => c i ω * A i ω with hξ
  have hξ4 : ∀ i < m, Integrable (fun ω => ξ i ω ^ 4) P := fun i hi =>
    (integrable_mul_of_memLp_two (memLp_pow_four_two (hc8 i hi))
      (memLp_pow_four_two (hAL i hi))).congr (ae_of_all _ fun ω => by simp only [hξ]; ring)
  have hξm : ∀ i < m, Measurable (ξ i) := fun i hi =>
    ((hcm i hi).mono ((pathFiltration B).le_ambient _) le_rfl).mul (hAa i hi)
  have hLp : ∀ i < m, MemLp (ξ i) 4 P := fun i hi =>
    memLp_four_of_integrable_pow_four (hξm i hi).aestronglyMeasurable (hξ4 i hi)
  have hsq : ∀ i < m, Real.sqrt (∫ ω, ξ i ω ^ 4 ∂P) ≤
      root4 Cc * root4 CA * (τ (i + 1) - τ i) ^ 2 := by
    intro i hi
    have hδ : 0 ≤ τ (i + 1) - τ i := sub_nonneg.mpr (hstep i)
    have hcs := abs_integral_mul_le_sqrt (memLp_pow_four_two (hc8 i hi))
      (memLp_pow_four_two (hAL i hi))
    have he1 : ∫ ω, ξ i ω ^ 4 ∂P = ∫ ω, c i ω ^ 4 * A i ω ^ 4 ∂P := by
      congr 1; funext ω; simp only [hξ]; ring
    have he2 : ∀ f : Ω → ℝ, ∫ ω, (f ω ^ 4) ^ 2 ∂P = ∫ ω, f ω ^ 8 ∂P := fun f => by
      congr 1; funext ω; ring
    rw [he2, he2] at hcs
    have hb : ∫ ω, ξ i ω ^ 4 ∂P ≤ Real.sqrt Cc * (Real.sqrt CA * (τ (i + 1) - τ i) ^ 4) := by
      rw [he1]
      refine (le_abs_self _).trans (hcs.trans ?_)
      refine mul_le_mul (Real.sqrt_le_sqrt (hCc i hi)) ?_ (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
      calc Real.sqrt (∫ ω, A i ω ^ 8 ∂P) ≤ Real.sqrt (CA * (τ (i + 1) - τ i) ^ 8) :=
            Real.sqrt_le_sqrt (hA8 i hi).2
        _ = Real.sqrt CA * (τ (i + 1) - τ i) ^ 4 := by
            rw [Real.sqrt_mul hCA0, show (τ (i + 1) - τ i) ^ 8 = ((τ (i + 1) - τ i) ^ 4) ^ 2 by
              ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (∫ ω, ξ i ω ^ 4 ∂P)
        ≤ Real.sqrt (Real.sqrt Cc * (Real.sqrt CA * (τ (i + 1) - τ i) ^ 4)) :=
          Real.sqrt_le_sqrt hb
      _ = root4 Cc * root4 CA * (τ (i + 1) - τ i) ^ 2 := by
          rw [Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_mul (Real.sqrt_nonneg _),
            show (τ (i + 1) - τ i) ^ 4 = ((τ (i + 1) - τ i) ^ 2) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]
          simp only [root4]; ring
  have horth : ∀ j < m, ∫ ω, (∑ i ∈ range j, ξ i ω) ^ 3 * ξ j ω ^ 1 ∂P = 0 := by
    intro j hj
    have hSm : Measurable[(pathFiltration B).σAlg (τ j)] (fun ω => ∑ i ∈ range j, ξ i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hij : i < j := mem_range.mp hi
      exact ((hcm i (hij.trans hj)).mono ((pathFiltration B).mono (hτ hij.le)) le_rfl).mul
        (hAm i (hij.trans hj) (τ j) (hτ (Nat.succ_le_of_lt hij)))
    have hgm : Measurable[(pathFiltration B).σAlg (τ j)]
        (fun ω => (∑ i ∈ range j, ξ i ω) ^ 3 * c j ω) := (hSm.pow_const 3).mul (hcm j hj)
    have hSL : MemLp (fun ω => ∑ i ∈ range j, ξ i ω) 4 P := by
      have h := memLp_finsetSum' (p := 4) (μ := P) (range j) (f := ξ)
        fun i hi => hLp i ((mem_range.mp hi).trans hj)
      have hfun : (∑ i ∈ range j, ξ i) = fun ω => ∑ i ∈ range j, ξ i ω := by
        funext ω; simp
      rwa [hfun] at h
    have hint : Integrable (fun ω => (∑ i ∈ range j, ξ i ω) ^ 3 * c j ω *
        frozenIncr B hd H (τ j) (τ (j + 1)) ω) P := by
      refine ((integrable_pow_of_memLp_four hSL (k := 4) le_rfl).add (hξ4 j hj)).mono'
        ((hgm.mono ((pathFiltration B).le_ambient _) le_rfl).mul
          (hAa j hj)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      have h := abs_pow_three_mul_le (∑ i ∈ range j, ξ i ω) (ξ j ω)
      simp only [hξ, hAdef] at h ⊢
      rw [show (∑ i ∈ range j, c i ω * frozenIncr B hd H (τ i) (τ (i + 1)) ω) ^ 3 * c j ω *
          frozenIncr B hd H (τ j) (τ (j + 1)) ω =
        (∑ i ∈ range j, c i ω * frozenIncr B hd H (τ i) (τ (i + 1)) ω) ^ 3 *
          (c j ω * frozenIncr B hd H (τ j) (τ (j + 1)) ω) by ring]
      exact h
    have h0 := integral_mul_frozenIncr_eq_zero B hd hH4 (hτn j) (hstep j) (hle j hj) hgm hint
    rw [← h0]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hξ, hAdef]; ring
  refine (integral_sum_pow_four_le_of_orthogonal m hLp horth).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Finset.mul_sum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)
    (Finset.sum_le_sum fun i hi => hsq i (mem_range.mp hi)) 2

end FrozenOrth

end SignatureVolatility
