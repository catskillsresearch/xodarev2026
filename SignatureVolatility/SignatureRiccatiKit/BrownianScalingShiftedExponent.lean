module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ItoCalculusKit.JointPast
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ProlongedBrownianSetup.ShiftedWordIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# B5a. Brownian scaling of the shifted exponent at factor `λ^{1/3}`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `λ`-scaled shifted Doléans exponent over `[0, s]` starting from `x`. -/
noncomputable def counterexampleV1ExponentScaled {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (lam s x : ℝ) (ω : Ω) : ℝ :=
  let w := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
  (lam / 3) * ((x + w s) ^ 3 - x ^ 3)
    - lam * (∫ r in (0 : ℝ)..s, (x + w r))
    - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..s, (x + w r) ^ 4)

/-- Law of `N` uniform increments `(ΔW_0, …, ΔW_{N-1})` on `[0, s]`:
i.i.d. `N(0, s / N)` Gaussians. -/
lemma hasLaw_incrVec {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) (N : ℕ) (hN : 0 < N) :
    let Δ := s / (N : ℝ)
    HasLaw (fun ω (k : Fin N) => wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω)
      (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal Δ)) P := by
  intro Δ
  have hΔ : 0 < Δ := div_pos hs (Nat.cast_pos.mpr hN)
  have hΔ0 : 0 ≤ Δ := hΔ.le
  have hpref : ∀ m ≤ N,
      HasLaw (fun ω (k : Fin m) => wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω)
        (Measure.pi fun _ : Fin m => gaussianReal 0 (Real.toNNReal Δ)) P := by
    intro m hm
    induction m with
    | zero =>
      have hfun :
          (fun ω (k : Fin 0) => wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω) =
            fun _ => (isEmptyElim : Fin 0 → ℝ) :=
        funext fun _ => funext fun k => k.elim0
      rw [hfun]
      refine ⟨measurable_const.aemeasurable, ?_⟩
      rw [Measure.map_const, measure_univ, one_smul, Measure.pi_of_empty]
    | succ m ih =>
      have ih' := ih (Nat.le_of_succ_le hm)
      set prev : Ω → Fin m → ℝ :=
        fun ω k => wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω
      set last : Ω → ℝ :=
        fun ω => wnnIncr B ⟨0, hd⟩ ((m : ℝ) * Δ) (((m + 1 : ℕ) : ℝ) * Δ) ω
      have hsu : (m : ℝ) * Δ ≤ ((m + 1 : ℕ) : ℝ) * Δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) hΔ0
      have hmΔ : 0 ≤ (m : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
      have hcoords : ∀ k : Fin m,
          Measurable[(pathFiltration B).σAlg ((m : ℝ) * Δ)] (fun ω => prev ω k) :=
        fun k => measurable_wnnIncr_pathFiltration B ⟨0, hd⟩
          (mul_nonneg (Nat.cast_nonneg _) hΔ0)
          (mul_nonneg (Nat.cast_nonneg _) hΔ0)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast k.isLt.le) hΔ0)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.succ_le_of_lt k.isLt)) hΔ0)
      have hprev_m : Measurable[(pathFiltration B).σAlg ((m : ℝ) * Δ)] prev :=
        (@measurable_pi_iff Ω (Fin m) (fun _ => ℝ)
          ((pathFiltration B).σAlg ((m : ℝ) * Δ)) _ prev).mpr hcoords
      have hind : IndepFun prev last P :=
        indepFun_pathFiltration_wnnIncr B ⟨0, hd⟩ hsu hprev_m
      have hlast_law : HasLaw last (gaussianReal 0 (Real.toNNReal Δ)) P := by
        have h := hasLaw_wnnIncr B ⟨0, hd⟩ hmΔ hsu
        have hsub : ((m + 1 : ℕ) : ℝ) * Δ - (m : ℝ) * Δ = Δ := by push_cast; ring
        rwa [hsub] at h
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => gaussianReal 0 (Real.toNNReal Δ)) (Fin.last m)
      have hpair : HasLaw (fun ω => (last ω, prev ω))
          ((gaussianReal 0 (Real.toNNReal Δ)).prod
            (Measure.pi fun _ : Fin m => gaussianReal 0 (Real.toNNReal Δ))) P :=
        ⟨(measurable_wnnIncr B ⟨0, hd⟩ _ _).aemeasurable.prodMk ih'.aemeasurable, by
          rw [(indepFun_iff_map_prod_eq_prod_map_map
            (measurable_wnnIncr B ⟨0, hd⟩ _ _).aemeasurable ih'.aemeasurable).mp hind.symm,
            hlast_law.map_eq, ih'.map_eq]⟩
      have hcomp := (hmp.symm e).fun_comp_hasLaw hpair
      have heq : (fun ω => e.symm (last ω, prev ω)) =
          fun ω (k : Fin (m + 1)) =>
            wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω := by
        funext ω; ext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [e, last]
        · simp [e, prev]
      rwa [heq] at hcomp
  exact hpref N le_rfl

/-- Scaling a product of i.i.d. `N(0, Δ)` Gaussians by `c > 0` gives i.i.d. `N(0, c² Δ)`. -/
private lemma hasLaw_smul_incrVec {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s c : ℝ} (hs : 0 < s) (_hc : 0 < c) (N : ℕ) (hN : 0 < N) :
    let Δ := s / (N : ℝ)
    let Δ' := (c ^ 2 * s) / (N : ℝ)
    HasLaw (fun ω (k : Fin N) => c * wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω)
      (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal Δ')) P := by
  intro Δ Δ'
  have hlaw := hasLaw_incrVec B hd hs N hN
  have hΔ : 0 < Δ := div_pos hs (Nat.cast_pos.mpr hN)
  have hΔ'0 : 0 ≤ Δ' := div_nonneg (mul_nonneg (sq_nonneg _) hs.le) (Nat.cast_nonneg _)
  have hf : Measurable fun (z : Fin N → ℝ) (k : Fin N) => c * z k :=
    measurable_pi_iff.mpr fun k => measurable_const.mul (measurable_pi_apply k)
  have hmap : HasLaw (fun (z : Fin N → ℝ) (k : Fin N) => c * z k)
      (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal Δ'))
      (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal Δ)) := by
    refine ⟨hf.aemeasurable, ?_⟩
    have hpi :
        (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal Δ)).map
          (fun (z : Fin N → ℝ) (k : Fin N) => c * z k) =
        Measure.pi fun _ : Fin N =>
          (gaussianReal 0 (Real.toNNReal Δ)).map (c * ·) :=
      Measure.pi_map_pi (fun _ : Fin N => (measurable_const.mul measurable_id).aemeasurable)
    rw [hpi]
    congr 1
    funext _
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ hΔ.le, Real.coe_toNNReal _ hΔ'0]
      change c ^ 2 * Δ = Δ'
      simp only [Δ, Δ']
      ring
  exact hmap.fun_comp hlaw

/-- Discrete left Riemann approximation of `counterexampleV1Exponent` on `N` steps. -/
noncomputable def discV1Exp (N : ℕ) (s x : ℝ) (z : Fin N → ℝ) : ℝ :=
  let Δ := s / (N : ℝ)
  let psum : ℕ → ℝ := fun k => ∑ j : Fin N, if (j : ℕ) < k then z j else 0
  (1 / 3 : ℝ) * ((x + psum N) ^ 3 - x ^ 3)
    - (∑ k : Fin N, (x + psum k) * Δ)
    - (1 / 2 : ℝ) * (∑ k : Fin N, (x + psum k) ^ 4 * Δ)

lemma continuous_discV1Exp (N : ℕ) (s x : ℝ) :
    Continuous fun z : Fin N → ℝ => discV1Exp N s x z := by
  have hp (k : ℕ) : Continuous fun z : Fin N → ℝ =>
      ∑ j : Fin N, if (j : ℕ) < k then z j else 0 :=
    continuous_finsetSum _ fun j _ => by
      by_cases hj : (j : ℕ) < k
      · simpa [hj] using (continuous_apply j : Continuous fun z : Fin N → ℝ => z j)
      · simpa [hj] using (continuous_const : Continuous fun _ : Fin N → ℝ => (0 : ℝ))
  have hpsumN : Continuous fun z : Fin N → ℝ =>
      (1 / 3 : ℝ) * ((x + (∑ j : Fin N, if (j : ℕ) < N then z j else 0)) ^ 3 - x ^ 3) :=
    continuous_const.mul ((((hp N).const_add x).pow 3).sub continuous_const)
  have hsum1 : Continuous fun z : Fin N → ℝ =>
      ∑ k : Fin N, (x + (∑ j : Fin N, if (j : ℕ) < (k : ℕ) then z j else 0)) * (s / (N : ℝ)) :=
    continuous_finsetSum _ fun k _ => ((hp (k : ℕ)).const_add x).mul continuous_const
  have hsum4 : Continuous fun z : Fin N → ℝ =>
      (1 / 2 : ℝ) * ∑ k : Fin N,
        (x + (∑ j : Fin N, if (j : ℕ) < (k : ℕ) then z j else 0)) ^ 4 * (s / (N : ℝ)) :=
    continuous_const.mul <| continuous_finsetSum _ fun k _ =>
      (((hp (k : ℕ)).const_add x).pow 4).mul continuous_const
  unfold discV1Exp
  convert (hpsumN.sub hsum1).sub hsum4

lemma psum_incrVec {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (s : ℝ) (N k : ℕ) (hk : k ≤ N) (ω : Ω) :
    (∑ j : Fin N, if (j : ℕ) < k then
      wnnIncr B ⟨0, hd⟩ ((j : ℝ) * (s / (N : ℝ))) (((j : ℕ) + 1 : ℕ) * (s / (N : ℝ))) ω else 0) =
    MultiBrownian.W B ((k : ℝ) * (s / (N : ℝ))) ω ⟨0, hd⟩ := by
  have hfilter : (Finset.range N).filter (fun a : ℕ => a < k) = Finset.range k := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun ha => ⟨ha.trans_le hk, ha⟩⟩
  have hsum :
      (∑ j : Fin N, if (j : ℕ) < k then
        wnnIncr B ⟨0, hd⟩ ((j : ℝ) * (s / (N : ℝ))) (((j : ℕ) + 1 : ℕ) * (s / (N : ℝ))) ω
        else 0) =
      ∑ j ∈ Finset.range k,
        wnnIncr B ⟨0, hd⟩ ((j : ℝ) * (s / (N : ℝ))) (((j + 1 : ℕ) : ℝ) * (s / (N : ℝ))) ω := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      if j < k then
        wnnIncr B ⟨0, hd⟩ ((j : ℝ) * (s / (N : ℝ))) (((j + 1 : ℕ) : ℝ) * (s / (N : ℝ))) ω
        else 0) N]
    simp only [← Finset.sum_filter]
    rw [hfilter]
  rw [hsum]
  simp only [wnnIncr_eq_W]
  simpa [MultiBrownian.W_zero] using
    (Finset.sum_range_sub (fun j => MultiBrownian.W B ((j : ℝ) * (s / (N : ℝ))) ω ⟨0, hd⟩) k)

lemma continuous_W_coord_v1 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (ω : Ω) :
    Continuous fun t : ℝ => MultiBrownian.W B t ω k :=
  (B.pathContinuous k ω).comp continuous_real_toNNReal

lemma measurable_intervalIntegral_addW {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k := by
  have hsum : ∀ n : ℕ, Measurable fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      ((MultiBrownian.W_meas B _ k).const_add x).mul_const _
  have hlim : ∀ ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k)) := fun ω =>
    tendsto_lebRiemann_of_continuousOn hs
      (continuous_const.add (continuous_W_coord_v1 B k ω)).continuousOn
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

lemma measurable_intervalIntegral_addW_pow4 {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4 := by
  have hsum : ∀ n : ℕ, Measurable fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) ^ 4 *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      (((MultiBrownian.W_meas B _ k).const_add x).pow_const 4).mul_const _
  have hlim : ∀ ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) ω k) ^ 4 *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4)) := fun ω =>
    tendsto_lebRiemann_of_continuousOn hs
      ((continuous_const.add (continuous_W_coord_v1 B k ω)).pow 4).continuousOn
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

lemma measurable_counterexampleV1Exponent {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => counterexampleV1Exponent B hd s x ω := by
  have hW : Measurable fun ω => MultiBrownian.W B s ω ⟨0, hd⟩ :=
    MultiBrownian.W_meas B s ⟨0, hd⟩
  have hI := measurable_intervalIntegral_addW B ⟨0, hd⟩ hs x
  have hQ := measurable_intervalIntegral_addW_pow4 B ⟨0, hd⟩ hs x
  simp only [counterexampleV1Exponent]
  exact (((hW.const_add x).pow_const 3).sub measurable_const).const_mul _ |>.sub hI |>.sub
    (hQ.const_mul _)

lemma measurable_counterexampleV1ExponentScaled {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {lam s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Measurable fun ω => counterexampleV1ExponentScaled B hd lam s x ω := by
  have hW : Measurable fun ω => MultiBrownian.W B s ω ⟨0, hd⟩ :=
    MultiBrownian.W_meas B s ⟨0, hd⟩
  have hI := measurable_intervalIntegral_addW B ⟨0, hd⟩ hs x
  have hQ := measurable_intervalIntegral_addW_pow4 B ⟨0, hd⟩ hs x
  simp only [counterexampleV1ExponentScaled]
  exact (((hW.const_add x).pow_const 3).sub measurable_const).const_mul _ |>.sub
    (hI.const_mul _) |>.sub (hQ.const_mul _)

lemma measurable_min_exp_disc (N : ℕ) (s x : ℝ) (R : ℕ)
    {Z : Ω → Fin N → ℝ} (hZ : Measurable Z) :
    Measurable fun ω => min (R : ℝ) (Real.exp (discV1Exp N s x (Z ω))) :=
  measurable_const.min (Real.measurable_exp.comp ((continuous_discV1Exp N s x).measurable.comp hZ))

/-- Brownian scaling in **expectation** (full strength, zero path-space machinery). -/
lemma brownian_scaling_shiftedExponent {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (x : ℝ) :
    ∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P =
      counterexampleV1 B hd (lam ^ (2 / 3 : ℝ) * s) (lam ^ (1 / 3 : ℝ) * x) := by
  rcases hs.eq_or_lt with rfl | hs_pos
  · simp [counterexampleV1ExponentScaled, counterexampleV1, counterexampleV1Exponent,
      MultiBrownian.W_zero]
  set c : ℝ := lam ^ (1 / 3 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hlam _
  have hc2 : c ^ 2 = lam ^ (2 / 3 : ℝ) := by
    rw [show c = lam ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  have hc3 : c ^ 3 = lam := by
    rw [show c = lam ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  set s' : ℝ := c ^ 2 * s
  set x' : ℝ := c * x
  have hs' : 0 < s' := mul_pos (sq_pos_of_pos hc) hs_pos
  rw [← hc2]
  change ∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P =
    ∫ ω, Real.exp (counterexampleV1Exponent B hd s' x' ω) ∂P
  have hcut : ∀ R : ℕ,
      ∫ ω, min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) ∂P =
        ∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s' x' ω)) ∂P := by
    intro R
    let Z (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ := fun k =>
      c * wnnIncr B ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω
    let Z' (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ := fun k =>
      wnnIncr B ⟨0, hd⟩ ((k : ℝ) * (s' / ((n + 1 : ℕ) : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s' / ((n + 1 : ℕ) : ℝ))) ω
    have hZ : ∀ n, Measurable (Z n) := fun n =>
      measurable_pi_iff.mpr fun k => measurable_const.mul (measurable_wnnIncr B ⟨0, hd⟩ _ _)
    have hZ' : ∀ n, Measurable (Z' n) := fun n =>
      measurable_pi_iff.mpr fun k => measurable_wnnIncr B ⟨0, hd⟩ _ _
    have hfin : ∀ n : ℕ,
        ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s' x' (Z n ω))) ∂P =
          ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s' x' (Z' n ω))) ∂P := fun n => by
      have hcont := continuous_discV1Exp (n + 1) s' x'
      have hcont' : Continuous fun z : Fin (n + 1) → ℝ =>
          min (R : ℝ) (Real.exp (discV1Exp (n + 1) s' x' z)) :=
        continuous_const.min (Real.continuous_exp.comp hcont)
      have h1 := (hasLaw_smul_incrVec B hd hs_pos hc (n + 1) n.succ_pos).integral_comp
        hcont'.aestronglyMeasurable
      have h2 := (hasLaw_incrVec B hd hs' (n + 1) n.succ_pos).integral_comp
        hcont'.aestronglyMeasurable
      exact h1.trans h2.symm
    have hLHS : Tendsto (fun n => ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s' x' (Z n ω))) ∂P)
        atTop (𝓝 (∫ ω, min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (R : ℝ))
        (fun n => (measurable_min_exp_disc (n + 1) s' x' R (hZ n)).aestronglyMeasurable)
        (integrable_const _)
        (fun n => ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
          exact min_le_left _ _)
        (ae_of_all _ fun ω => by
          have hc1 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x + MultiBrownian.W B ((j : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                (s / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω ⟨0, hd⟩)) :=
            tendsto_lebRiemann_of_continuousOn hs_pos.le
              (continuous_const.add (continuous_W_coord_v1 B ⟨0, hd⟩ ω)).continuousOn
          have hc4 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x + MultiBrownian.W B ((j : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                (s / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4)) :=
            tendsto_lebRiemann_of_continuousOn hs_pos.le
              ((continuous_const.add (continuous_W_coord_v1 B ⟨0, hd⟩ ω)).pow 4).continuousOn
          have hlim : Tendsto (fun n => discV1Exp (n + 1) s' x' (Z n ω)) atTop
              (𝓝 (counterexampleV1ExponentScaled B hd lam s x ω)) := by
            have h := ((tendsto_const_nhds (x := (lam / 3) *
              ((x + MultiBrownian.W B s ω ⟨0, hd⟩) ^ 3 - x ^ 3))).sub
              (hc1.const_mul lam)).sub (hc4.const_mul (lam ^ 2 / 2))
            refine h.congr fun n => ?_
            have hpsum : ∀ k ≤ n + 1,
                (∑ j : Fin (n + 1), if (j : ℕ) < k then Z n ω j else 0) =
                  c * MultiBrownian.W B ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩ :=
              fun k hk => by
                have hZsum :
                    (∑ j : Fin (n + 1), if (j : ℕ) < k then Z n ω j else 0) =
                      c * (∑ j : Fin (n + 1), if (j : ℕ) < k then
                        wnnIncr B ⟨0, hd⟩ ((j : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
                          (((j : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω else 0) := by
                  dsimp only [Z]
                  simp [mul_ite, mul_zero, Finset.mul_sum]
                rw [hZsum, psum_incrVec B hd s (n + 1) k hk ω]
            have hNs : ((n + 1 : ℕ) : ℝ) * (s / ((n + 1 : ℕ) : ℝ)) = s := by field_simp
            have hsum1 :
                ∑ k : Fin (n + 1),
                  (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z n ω j else 0) *
                    (s' / ((n + 1 : ℕ) : ℝ)) =
                lam * ∑ k ∈ Finset.range (n + 1),
                  (x + MultiBrownian.W B ((k : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                    (s / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z n ω j else 0) *
                  (s' / ((n + 1 : ℕ) : ℝ))) (n + 1), Finset.mul_sum]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [hpsum k (Finset.mem_range.mp hk).le]
              simp only [x', s', ← hc3]
              push_cast
              ring
            have hsum4 :
                ∑ k : Fin (n + 1),
                  (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z n ω j else 0) ^ 4 *
                    (s' / ((n + 1 : ℕ) : ℝ)) =
                lam ^ 2 * ∑ k ∈ Finset.range (n + 1),
                  (x + MultiBrownian.W B ((k : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                    (s / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z n ω j else 0) ^ 4 *
                  (s' / ((n + 1 : ℕ) : ℝ))) (n + 1), Finset.mul_sum]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [hpsum k (Finset.mem_range.mp hk).le]
              simp only [x', s', ← hc3]
              push_cast
              ring
            simp only [discV1Exp]
            rw [hpsum (n + 1) le_rfl, hNs, hsum1, hsum4]
            simp only [x', ← hc3]
            ring
          exact tendsto_const_nhds.min ((Real.continuous_exp.tendsto _).comp hlim))
    have hRHS : Tendsto (fun n => ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s' x' (Z' n ω))) ∂P)
        atTop (𝓝 (∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s' x' ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (R : ℝ))
        (fun n => (measurable_min_exp_disc (n + 1) s' x' R (hZ' n)).aestronglyMeasurable)
        (integrable_const _)
        (fun n => ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
          exact min_le_left _ _)
        (ae_of_all _ fun ω => by
          have hc1 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x' + MultiBrownian.W B ((j : ℝ) * (s' / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                (s' / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s', x' + MultiBrownian.W B r ω ⟨0, hd⟩)) :=
            tendsto_lebRiemann_of_continuousOn hs'.le
              (continuous_const.add (continuous_W_coord_v1 B ⟨0, hd⟩ ω)).continuousOn
          have hc4 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x' + MultiBrownian.W B ((j : ℝ) * (s' / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                (s' / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s', (x' + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4)) :=
            tendsto_lebRiemann_of_continuousOn hs'.le
              ((continuous_const.add (continuous_W_coord_v1 B ⟨0, hd⟩ ω)).pow 4).continuousOn
          have hlim : Tendsto (fun n => discV1Exp (n + 1) s' x' (Z' n ω)) atTop
              (𝓝 (counterexampleV1Exponent B hd s' x' ω)) := by
            have h := ((tendsto_const_nhds (x := (1 / 3 : ℝ) *
              ((x' + MultiBrownian.W B s' ω ⟨0, hd⟩) ^ 3 - x' ^ 3))).sub hc1).sub
              (hc4.const_mul (1 / 2 : ℝ))
            refine h.congr fun n => ?_
            have hNs' : ((n + 1 : ℕ) : ℝ) * (s' / ((n + 1 : ℕ) : ℝ)) = s' := by field_simp
            have hsum1 :
                ∑ k : Fin (n + 1),
                  (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z' n ω j else 0) *
                    (s' / ((n + 1 : ℕ) : ℝ)) =
                ∑ k ∈ Finset.range (n + 1),
                  (x' + MultiBrownian.W B ((k : ℝ) * (s' / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                    (s' / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z' n ω j else 0) *
                  (s' / ((n + 1 : ℕ) : ℝ))) (n + 1)]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [psum_incrVec B hd s' (n + 1) k (Finset.mem_range.mp hk).le ω]
              push_cast
              rfl
            have hsum4 :
                ∑ k : Fin (n + 1),
                  (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z' n ω j else 0) ^ 4 *
                    (s' / ((n + 1 : ℕ) : ℝ)) =
                ∑ k ∈ Finset.range (n + 1),
                  (x' + MultiBrownian.W B ((k : ℝ) * (s' / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                    (s' / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z' n ω j else 0) ^ 4 *
                  (s' / ((n + 1 : ℕ) : ℝ))) (n + 1)]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [psum_incrVec B hd s' (n + 1) k (Finset.mem_range.mp hk).le ω]
              push_cast
              rfl
            simp only [discV1Exp]
            rw [psum_incrVec B hd s' (n + 1) (n + 1) le_rfl ω, hNs', hsum1, hsum4]
          exact tendsto_const_nhds.min ((Real.continuous_exp.tendsto _).comp hlim))
    exact tendsto_nhds_unique hLHS (hRHS.congr fun n => (hfin n).symm)
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s' x' ω)) ∂P := by
    have hMCT_L := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
      (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (R : ℝ)
        (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω))))
      (fun R => (measurable_const.min (Real.measurable_exp.comp
        (measurable_counterexampleV1ExponentScaled B hd hs_pos.le x))).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal (min_le_min_right _ (Nat.cast_le.mpr h12)))
      (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_atTop_of_eventually_const
        (i₀ := ⌈Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)⌉₊) fun R hR =>
          min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
    have hMCT_R := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
      (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (R : ℝ)
        (Real.exp (counterexampleV1Exponent B hd s' x' ω))))
      (fun R => (measurable_const.min (Real.measurable_exp.comp
        (measurable_counterexampleV1Exponent B hd hs'.le x'))).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal (min_le_min_right _ (Nat.cast_le.mpr h12)))
      (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_atTop_of_eventually_const
        (i₀ := ⌈Real.exp (counterexampleV1Exponent B hd s' x' ω)⌉₊) fun R hR =>
          min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
    refine tendsto_nhds_unique hMCT_L (hMCT_R.congr fun R => ?_)
    have hiL : Integrable (fun ω => min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω))) P :=
      (integrable_const (R : ℝ)).mono'
        (measurable_const.min (Real.measurable_exp.comp
          (measurable_counterexampleV1ExponentScaled B hd hs_pos.le x))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_left _ _)
    have hiR : Integrable (fun ω => min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s' x' ω))) P :=
      (integrable_const (R : ℝ)).mono'
        (measurable_const.min (Real.measurable_exp.comp
          (measurable_counterexampleV1Exponent B hd hs'.le x'))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_left _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hiR (ae_of_all _ fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal hiL (ae_of_all _ fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
      hcut R]
  by_cases h1 : Integrable (fun ω => Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) P
  · have h2 : Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s' x' ω)) P := by
      refine ⟨(Real.measurable_exp.comp (measurable_counterexampleV1Exponent B hd hs'.le x')).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      rw [← hlint]
      simpa [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal (Real.exp_pos _).le]
        using h1.hasFiniteIntegral
    have hL : ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) ∂P :=
      ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    have hR : ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B hd s' x' ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s' x' ω)) ∂P :=
      ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    calc ∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P
        = (ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P)).toReal :=
          (ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)).symm
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω)) ∂P).toReal :=
          congrArg ENNReal.toReal hL
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s' x' ω)) ∂P).toReal :=
          congrArg ENNReal.toReal hlint
      _ = (ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B hd s' x' ω) ∂P)).toReal :=
          congrArg ENNReal.toReal hR.symm
      _ = ∫ ω, Real.exp (counterexampleV1Exponent B hd s' x' ω) ∂P :=
          ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)
  · have h2 : ¬ Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s' x' ω)) P := by
      intro hi2; apply h1
      refine ⟨(Real.measurable_exp.comp
        (measurable_counterexampleV1ExponentScaled B hd hs_pos.le x)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      rw [hlint]
      simpa [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal (Real.exp_pos _).le]
        using hi2.hasFiniteIntegral
    rw [integral_undef h1, integral_undef h2]


/-- `counterexampleV1` depends only on the law of the driving Brownian motion, so it is
invariant under restarting at time `t`. -/
lemma counterexampleV1_eq_shift {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {t s : ℝ} (_ht : 0 ≤ t) (hs : 0 ≤ s) (x : ℝ) :
    counterexampleV1 (B.shift t.toNNReal) hd s x = counterexampleV1 B hd s x := by
  rcases hs.eq_or_lt with rfl | hs_pos
  · simp [counterexampleV1, counterexampleV1Exponent, MultiBrownian.W_zero]
  set B' := B.shift t.toNNReal
  have hcut : ∀ R : ℕ,
      ∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B' hd s x ω)) ∂P =
        ∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P := by
    intro R
    let Z (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ := fun k =>
      wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω
    let Z0 (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ := fun k =>
      wnnIncr B ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω
    have hZ : ∀ n, Measurable (Z n) := fun n =>
      measurable_pi_iff.mpr fun k => measurable_wnnIncr B' ⟨0, hd⟩ _ _
    have hZ0 : ∀ n, Measurable (Z0 n) := fun n =>
      measurable_pi_iff.mpr fun k => measurable_wnnIncr B ⟨0, hd⟩ _ _
    have hfin : ∀ n : ℕ,
        ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s x (Z n ω))) ∂P =
          ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s x (Z0 n ω))) ∂P := fun n => by
      have hcont := continuous_discV1Exp (n + 1) s x
      have hcont' : Continuous fun z : Fin (n + 1) → ℝ =>
          min (R : ℝ) (Real.exp (discV1Exp (n + 1) s x z)) :=
        continuous_const.min (Real.continuous_exp.comp hcont)
      have h1 := (hasLaw_incrVec B' hd hs_pos (n + 1) n.succ_pos).integral_comp
        hcont'.aestronglyMeasurable
      have h2 := (hasLaw_incrVec B hd hs_pos (n + 1) n.succ_pos).integral_comp
        hcont'.aestronglyMeasurable
      exact h1.trans h2.symm
    have hlim (B₀ : MultiBrownian Ω P d)
        (Z₀ : (n : ℕ) → Ω → Fin (n + 1) → ℝ)
        (hZ₀ : ∀ n, Measurable (Z₀ n))
        (hpsum₀ : ∀ n ω k, k ≤ n + 1 →
          (∑ j : Fin (n + 1), if (j : ℕ) < k then Z₀ n ω j else 0) =
            MultiBrownian.W B₀ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) :
        Tendsto (fun n => ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s x (Z₀ n ω))) ∂P)
          atTop (𝓝 (∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B₀ hd s x ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (R : ℝ))
        (fun n => (measurable_min_exp_disc (n + 1) s x R (hZ₀ n)).aestronglyMeasurable)
        (integrable_const _)
        (fun n => ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
          exact min_le_left _ _)
        (ae_of_all _ fun ω => by
          have hc1 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x + MultiBrownian.W B₀ ((j : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                (s / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s, x + MultiBrownian.W B₀ r ω ⟨0, hd⟩)) :=
            tendsto_lebRiemann_of_continuousOn hs_pos.le
              (continuous_const.add (continuous_W_coord_v1 B₀ ⟨0, hd⟩ ω)).continuousOn
          have hc4 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
              (x + MultiBrownian.W B₀ ((j : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                (s / ((n : ℝ) + 1))) atTop
              (𝓝 (∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B₀ r ω ⟨0, hd⟩) ^ 4)) :=
            tendsto_lebRiemann_of_continuousOn hs_pos.le
              ((continuous_const.add (continuous_W_coord_v1 B₀ ⟨0, hd⟩ ω)).pow 4).continuousOn
          have hlim' : Tendsto (fun n => discV1Exp (n + 1) s x (Z₀ n ω)) atTop
              (𝓝 (counterexampleV1Exponent B₀ hd s x ω)) := by
            have h := ((tendsto_const_nhds (x := (1 / 3 : ℝ) *
              ((x + MultiBrownian.W B₀ s ω ⟨0, hd⟩) ^ 3 - x ^ 3))).sub hc1).sub
              (hc4.const_mul (1 / 2 : ℝ))
            refine h.congr fun n => ?_
            have hNs : ((n + 1 : ℕ) : ℝ) * (s / ((n + 1 : ℕ) : ℝ)) = s := by field_simp
            have hsum1 :
                ∑ k : Fin (n + 1),
                  (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z₀ n ω j else 0) *
                    (s / ((n + 1 : ℕ) : ℝ)) =
                ∑ k ∈ Finset.range (n + 1),
                  (x + MultiBrownian.W B₀ ((k : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                    (s / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z₀ n ω j else 0) *
                  (s / ((n + 1 : ℕ) : ℝ))) (n + 1)]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [hpsum₀ n ω k (Finset.mem_range.mp hk).le]
              push_cast
              rfl
            have hsum4 :
                ∑ k : Fin (n + 1),
                  (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z₀ n ω j else 0) ^ 4 *
                    (s / ((n + 1 : ℕ) : ℝ)) =
                ∑ k ∈ Finset.range (n + 1),
                  (x + MultiBrownian.W B₀ ((k : ℝ) * (s / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                    (s / ((n : ℝ) + 1)) := by
              rw [Fin.sum_univ_eq_sum_range (fun k =>
                (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z₀ n ω j else 0) ^ 4 *
                  (s / ((n + 1 : ℕ) : ℝ))) (n + 1)]
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [hpsum₀ n ω k (Finset.mem_range.mp hk).le]
              push_cast
              rfl
            simp only [discV1Exp]
            rw [hpsum₀ n ω (n + 1) le_rfl, hNs, hsum1, hsum4]
          exact tendsto_const_nhds.min ((Real.continuous_exp.tendsto _).comp hlim'))
    have hpsumZ : ∀ n ω k, k ≤ n + 1 →
        (∑ j : Fin (n + 1), if (j : ℕ) < k then Z n ω j else 0) =
          MultiBrownian.W B' ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩ :=
      fun n ω k hk => by
        dsimp only [Z]
        exact psum_incrVec B' hd s (n + 1) k hk ω
    have hpsumZ0 : ∀ n ω k, k ≤ n + 1 →
        (∑ j : Fin (n + 1), if (j : ℕ) < k then Z0 n ω j else 0) =
          MultiBrownian.W B ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩ :=
      fun n ω k hk => by
        dsimp only [Z0]
        exact psum_incrVec B hd s (n + 1) k hk ω
    exact tendsto_nhds_unique (hlim B' Z hZ hpsumZ)
      ((hlim B Z0 hZ0 hpsumZ0).congr fun n => (hfin n).symm)
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B' hd s x ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P := by
    have hMCT (B₀ : MultiBrownian Ω P d) :=
      lintegral_tendsto_of_tendsto_of_monotone (μ := P)
        (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (R : ℝ)
          (Real.exp (counterexampleV1Exponent B₀ hd s x ω))))
        (fun R => (measurable_const.min (Real.measurable_exp.comp
          (measurable_counterexampleV1Exponent B₀ hd hs_pos.le x))).aemeasurable.ennreal_ofReal)
        (ae_of_all _ fun ω R₁ R₂ h12 =>
          ENNReal.ofReal_le_ofReal (min_le_min_right _ (Nat.cast_le.mpr h12)))
        (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_atTop_of_eventually_const
          (i₀ := ⌈Real.exp (counterexampleV1Exponent B₀ hd s x ω)⌉₊) fun R hR =>
            min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
    refine tendsto_nhds_unique (hMCT B') ((hMCT B).congr fun R => ?_)
    have hi (B₀ : MultiBrownian Ω P d) :
        Integrable (fun ω => min (R : ℝ) (Real.exp (counterexampleV1Exponent B₀ hd s x ω))) P :=
      (integrable_const (R : ℝ)).mono'
        (measurable_const.min (Real.measurable_exp.comp
          (measurable_counterexampleV1Exponent B₀ hd hs_pos.le x))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
          exact min_le_left _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi B) (ae_of_all _ fun _ =>
        le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal (hi B') (ae_of_all _ fun _ =>
        le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
      hcut R]
  -- Unfold the two `counterexampleV1` definitions and compare integrals.
  simp only [counterexampleV1]
  by_cases h1 : Integrable (fun ω => Real.exp (counterexampleV1Exponent B' hd s x ω)) P
  · have h2 : Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s x ω)) P := by
      refine ⟨(Real.measurable_exp.comp
        (measurable_counterexampleV1Exponent B hd hs_pos.le x)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      rw [← hlint]
      simpa [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal (Real.exp_pos _).le]
        using h1.hasFiniteIntegral
    have hL : ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B' hd s x ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B' hd s x ω)) ∂P :=
      ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    have hR : ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B hd s x ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P :=
      ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    calc ∫ ω, Real.exp (counterexampleV1Exponent B' hd s x ω) ∂P
        = (ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B' hd s x ω) ∂P)).toReal :=
          (ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)).symm
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B' hd s x ω)) ∂P).toReal :=
          congrArg ENNReal.toReal hL
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P).toReal :=
          congrArg ENNReal.toReal hlint
      _ = (ENNReal.ofReal (∫ ω, Real.exp (counterexampleV1Exponent B hd s x ω) ∂P)).toReal :=
          congrArg ENNReal.toReal hR.symm
      _ = ∫ ω, Real.exp (counterexampleV1Exponent B hd s x ω) ∂P :=
          ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)
  · have h2 : ¬ Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s x ω)) P := by
      intro hi2; apply h1
      refine ⟨(Real.measurable_exp.comp
        (measurable_counterexampleV1Exponent B' hd hs_pos.le x)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      rw [hlint]
      simpa [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal (Real.exp_pos _).le]
        using hi2.hasFiniteIntegral
    rw [integral_undef h1, integral_undef h2]


end SignatureVolatility
