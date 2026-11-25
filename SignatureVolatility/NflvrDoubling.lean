module

public import SignatureVolatility.NflvrDefs
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted
public import SignatureVolatility.ItoCalculusKit.MathFinBridge

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- First Brownian coordinate of a one-dimensional `MultiBrownian`, reindexed to `ℝ`. -/
def bmCoord (B : MultiBrownian Ω P 1) : ℝ → Ω → ℝ :=
  fun t ω => B.W t ω ⟨0, Nat.succ_pos 0⟩

lemma bmCoord_eq_wnn (B : MultiBrownian Ω P 1) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    bmCoord B t ω = B.Wnn ⟨t, ht⟩ ω ⟨0, Nat.succ_pos 0⟩ :=
  B.W_eq_Wnn_of_nonneg ht ω ⟨0, Nat.succ_pos 0⟩

lemma bmCoord_cont (B : MultiBrownian Ω P 1) (ω : Ω) :
    ContinuousOn (fun t : ℝ => bmCoord B t ω) (Ici 0) := by
  have hpath : Continuous fun s : ℝ≥0 => B.Wnn s ω ⟨0, Nat.succ_pos 0⟩ :=
    B.pathContinuous ⟨0, Nat.succ_pos 0⟩ ω
  apply (hpath.comp continuous_real_toNNReal).continuousOn.congr
  intro s hs
  have hs' : 0 ≤ s := mem_Ici.mp hs
  simp only [bmCoord, Function.comp_apply]
  rw [B.W_eq_Wnn_of_nonneg hs']
  congr 1
  exact (Real.toNNReal_of_nonneg hs').symm

lemma bmCoord_cont_Icc (B : MultiBrownian Ω P 1) (ω : Ω) {T : ℝ} (_hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => bmCoord B t ω) (Icc 0 T) :=
  (bmCoord_cont B ω).mono Icc_subset_Ici_self

lemma bmCoord_zero (B : MultiBrownian Ω P 1) (ω : Ω) : bmCoord B 0 ω = 0 :=
  B.W_zero ω ⟨0, Nat.succ_pos 0⟩

lemma bmCoord_meas (B : MultiBrownian Ω P 1) (t : ℝ) :
    Measurable (bmCoord B t) :=
  B.W_meas t ⟨0, Nat.succ_pos 0⟩

lemma bmCoord_adapted (B : MultiBrownian Ω P 1) {T : ℝ} {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Measurable[(pathFiltration B).σAlg T] (bmCoord B t) :=
  measurable_W_pathFiltration B ⟨t, ht.1, ht.2⟩ ⟨0, Nat.succ_pos 0⟩

lemma bmCoord_isPreBrownian (B : MultiBrownian Ω P 1) :
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => B.Wnn t ω ⟨0, Nat.succ_pos 0⟩) P :=
  (B.isBrownian ⟨0, Nat.succ_pos 0⟩).toIsPreBrownianReal

/-- Geometric grid `t_n = T (1 - 2^{-n})` and step `Δt_n = T · 2^{-(n+1)}`. -/
def tGrid (T : ℝ) (n : ℕ) : ℝ := T * (1 - (1 / 2 : ℝ) ^ n)

def dtGrid (T : ℝ) (n : ℕ) : ℝ := T * (1 / 2 : ℝ) ^ (n + 1)

lemma tGrid_zero (T : ℝ) : tGrid T 0 = 0 := by simp [tGrid]

lemma tGrid_succ_sub (T : ℝ) (n : ℕ) : tGrid T (n + 1) - tGrid T n = dtGrid T n := by
  simp only [tGrid, dtGrid, pow_succ]
  ring

lemma dtGrid_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < dtGrid T n := by
  unfold dtGrid
  positivity

lemma tGrid_mem {T : ℝ} (hT : 0 < T) (n : ℕ) : tGrid T n ∈ Icc 0 T := by
  unfold tGrid
  have h1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact ⟨mul_nonneg hT.le (sub_nonneg.mpr h1),
    mul_le_of_le_one_right hT.le (sub_le_self 1 (by positivity))⟩

lemma tGrid_lt_succ {T : ℝ} (hT : 0 < T) (n : ℕ) : tGrid T n < tGrid T (n + 1) := by
  linarith [tGrid_succ_sub T n, dtGrid_pos hT n]

lemma tGrid_lt_T {T : ℝ} (hT : 0 < T) (n : ℕ) : tGrid T n < T := by
  unfold tGrid
  have : 0 < (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

/-- Standardized increment `Z_n = (B_{t_{n+1}} - B_{t_n}) / √(Δt_n)`. -/
def stdIncr (B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (B (tGrid T (n + 1)) ω - B (tGrid T n) ω) / Real.sqrt (dtGrid T n)

/-- Times in the nth grid interval at which the increment reaches the threshold `√(Δt_n)`. -/
def hitSet (B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : Set ℝ :=
  {t ∈ Icc (tGrid T n) (tGrid T (n + 1)) |
    Real.sqrt (dtGrid T n) ≤ B t ω - B (tGrid T n) ω}

/-- First hitting time of `B_t - B_{t_n} = √(Δt_n)` on `[t_n, t_{n+1}]`, or `t_{n+1}` if none. -/
def tauHit (B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if (hitSet B T n ω).Nonempty then sInf (hitSet B T n ω) else tGrid T (n + 1)

/-- No hit of the threshold on the nth grid interval. -/
def noHitEvent (B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ t ∈ Icc (tGrid T n) (tGrid T (n + 1)),
    B t ω - B (tGrid T n) ω < Real.sqrt (dtGrid T n)}

/-- Hitting a closed threshold on `[a, t]` is equivalent to a countable rational condition. -/
lemma exists_hit_iff_rat {a t c : ℝ} (hat : a ≤ t) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a t)) :
    (∃ s ∈ Icc a t, c ≤ f s) ↔
      (∀ k : ℕ, (∃ q : ℚ, a ≤ (q : ℝ) ∧ (q : ℝ) ≤ t ∧ c - 1 / ((k : ℝ) + 1) < f q) ∨ c ≤ f t) := by
  constructor
  · rintro ⟨s, hs, hfs⟩ k
    rcases hs.2.eq_or_lt with rfl | hlt
    · exact Or.inr hfs
    · left
      have hpos : 0 < f s - (c - 1 / ((k : ℝ) + 1)) := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have hC : ContinuousWithinAt f (Icc a t) s := hf s hs
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp hC _ hpos
      obtain ⟨q, hsq, hqb⟩ := exists_rat_btwn (lt_min hlt (by linarith : s < s + δ))
      refine ⟨q, hs.1.trans hsq.le, (lt_of_lt_of_le hqb (min_le_left _ _)).le, ?_⟩
      have hqI : (q : ℝ) ∈ Icc a t :=
        ⟨hs.1.trans hsq.le, (lt_of_lt_of_le hqb (min_le_left _ _)).le⟩
      have hd : dist (q : ℝ) s < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsq)]
        linarith [lt_of_lt_of_le hqb (min_le_right _ _)]
      have h1 := hball hqI hd
      rw [Real.dist_eq, abs_lt] at h1
      linarith
  · intro hall
    by_cases hft : c ≤ f t
    · exact ⟨t, ⟨hat, le_rfl⟩, hft⟩
    · have hex : ∀ k : ℕ, ∃ q : ℚ, a ≤ (q : ℝ) ∧ (q : ℝ) ≤ t ∧ c - 1 / ((k : ℝ) + 1) < f q :=
        fun k => (hall k).resolve_right hft
      choose q hqa hqt hfq using hex
      obtain ⟨s, hs, φ, hφ_mono, hφ_lim⟩ :=
        isCompact_Icc.tendsto_subseq (x := fun k => (q k : ℝ)) (fun k => ⟨hqa k, hqt k⟩)
      refine ⟨s, hs, ?_⟩
      have hf_lim : Tendsto (fun k => f (q (φ k))) atTop (𝓝 (f s)) := by
        have hC : ContinuousWithinAt f (Icc a t) s := hf s hs
        have hφ_within :
            Tendsto (fun k => (q (φ k) : ℝ)) atTop (𝓝[Icc a t] s) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            hφ_lim (Eventually.of_forall fun k => ⟨hqa (φ k), hqt (φ k)⟩)
        exact hC.tendsto.comp hφ_within
      have hc_lim : Tendsto (fun k : ℕ => c - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 c) := by
        have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ 1
              (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop))
        simpa using tendsto_const_nhds.sub h0
      exact le_of_tendsto_of_tendsto hc_lim hf_lim (Eventually.of_forall fun k => (hfq (φ k)).le)

/-- `P(Z < 1) < 1` for a standard Gaussian. -/
lemma gaussian_Iio_one_lt_one : (gaussianReal 0 1) (Iio (1 : ℝ)) < 1 := by
  have hpos : 0 < (gaussianReal 0 1) (Ici (1 : ℝ)) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Ici]
    refine (setLIntegral_pos_iff (measurable_gaussianPDF 0 1)).mpr ?_
    have hsupp : Function.support (gaussianPDF 0 1) = Set.univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (gaussianPDF_pos 0 one_ne_zero x).ne'
    rw [hsupp, Set.univ_inter, Real.volume_Ici]
    exact ENNReal.zero_lt_top
  have hadd : (gaussianReal 0 1) (Iio (1 : ℝ)) + (gaussianReal 0 1) (Ici (1 : ℝ)) = 1 := by
    have hdisj : Disjoint (Iio (1 : ℝ)) (Ici (1 : ℝ)) := Set.Iio_disjoint_Ici le_rfl
    rw [← measure_union hdisj measurableSet_Ici, Iio_union_Ici, measure_univ]
  have h1 : (gaussianReal 0 1) (Iio (1 : ℝ)) <
      (gaussianReal 0 1) (Iio (1 : ℝ)) + (gaussianReal 0 1) (Ici (1 : ℝ)) :=
    ENNReal.lt_add_right (measure_ne_top _ _) hpos.ne'
  rwa [hadd] at h1


lemma tauHit_mem_Icc {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    tauHit B T n ω ∈ Icc (tGrid T n) (tGrid T (n + 1)) := by
  simp only [tauHit]
  split_ifs with hne
  · have hlb : BddBelow (hitSet B T n ω) := ⟨tGrid T n, fun t ht => (mem_Icc.mp ht.1).1⟩
    refine ⟨le_csInf hne fun t ht => (mem_Icc.mp ht.1).1, ?_⟩
    obtain ⟨t0, ht0⟩ := hne
    exact (csInf_le hlb ht0).trans (mem_Icc.mp ht0.1).2
  · exact ⟨(tGrid_lt_succ hT n).le, le_rfl⟩

lemma tauHit_spec (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) (ω : Ω) :
    (ω ∈ noHitEvent (bmCoord B) T n → tauHit (bmCoord B) T n ω = tGrid T (n + 1) ∧
      bmCoord B (tGrid T (n + 1)) ω - bmCoord B (tGrid T n) ω < Real.sqrt (dtGrid T n)) ∧
    (ω ∉ noHitEvent (bmCoord B) T n →
      bmCoord B (tauHit (bmCoord B) T n ω) ω - bmCoord B (tGrid T n) ω =
        Real.sqrt (dtGrid T n)) := by
  set a := tGrid T n
  set b := tGrid T (n + 1)
  set c := Real.sqrt (dtGrid T n)
  set S := hitSet (bmCoord B) T n ω
  have hab : Icc a b ⊆ Ici (0 : ℝ) := fun t ht => (tGrid_mem hT n).1.trans ht.1
  have hf : ContinuousOn (fun u => bmCoord B u ω - bmCoord B a ω) (Icc a b) :=
    ((bmCoord_cont B ω).mono hab).sub continuousOn_const
  have hS_eq : S = Icc a b ∩ (fun u => bmCoord B u ω - bmCoord B a ω) ⁻¹' Ici c := by
    ext u; simp [S, hitSet, a, b, c, mem_preimage, mem_Ici]
  have hS_closed : IsClosed S := by
    rw [hS_eq]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  constructor
  · intro hA
    have hempty : ¬ S.Nonempty := by
      rintro ⟨t, htI, htc⟩; exact not_lt.mpr htc (hA t htI)
    have htau0 : tauHit (bmCoord B) T n ω = b := by
      simp [tauHit, S, hempty, b]
    exact ⟨htau0, hA b ⟨(tGrid_lt_succ hT n).le, le_rfl⟩⟩
  · intro hnA
    have hne : S.Nonempty := by
      unfold noHitEvent at hnA
      simp only [Set.mem_ofPred_eq, not_forall, not_lt] at hnA
      obtain ⟨t, htI, htc⟩ := hnA
      exact ⟨t, htI, htc⟩
    have htau : tauHit (bmCoord B) T n ω = sInf S := by
      simp [tauHit, S, hne]
    rw [htau]
    have hmem : sInf S ∈ S :=
      hS_closed.csInf_mem hne ⟨a, fun t ht => (mem_Icc.mp ht.1).1⟩
    have hge : c ≤ bmCoord B (sInf S) ω - bmCoord B a ω := hmem.2
    have hgt_a : a < sInf S := by
      rcases hmem.1.1.eq_or_lt with heq | hlt
      · exfalso; rw [← heq, sub_self] at hge
        have : 0 < c := Real.sqrt_pos.mpr (dtGrid_pos hT n)
        linarith
      · exact hlt
    have hle : bmCoord B (sInf S) ω - bmCoord B a ω ≤ c := by
      by_contra hgt; push Not at hgt
      have hC : ContinuousWithinAt (fun u => bmCoord B u ω - bmCoord B a ω) (Icc a b) (sInf S) :=
        hf (sInf S) hmem.1
      obtain ⟨δ, hδ, hball⟩ :=
        Metric.continuousWithinAt_iff.mp hC ((bmCoord B (sInf S) ω - bmCoord B a ω - c) / 2)
          (by linarith)
      set s := max a (sInf S - δ / 2)
      have hs_lt : s < sInf S := max_lt hgt_a (by linarith)
      have hsI : s ∈ Icc a b := ⟨le_max_left _ _, hs_lt.le.trans hmem.1.2⟩
      have hd : dist s (sInf S) < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt)]
        have : sInf S - δ / 2 ≤ s := le_max_right _ _
        linarith
      have h1 := hball hsI hd
      rw [Real.dist_eq, abs_lt] at h1
      have hsS : s ∈ S := ⟨hsI, by linarith⟩
      exact not_le.mpr hs_lt (csInf_le ⟨a, fun t ht => ht.1.1⟩ hsS)
    exact le_antisymm hle hge

lemma noHitEvent_subset_stdIncr {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (n : ℕ) :
    noHitEvent B T n ⊆ {ω | stdIncr B T n ω < 1} := by
  intro ω hω
  simp only [mem_ofPred_eq, stdIncr]
  rw [div_lt_one (Real.sqrt_pos.mpr (dtGrid_pos hT n))]
  exact hω (tGrid T (n + 1)) ⟨(tGrid_lt_succ hT n).le, le_rfl⟩

lemma nndist_of_le {s t : ℝ} (hst : s ≤ t) : nndist s t = Real.toNNReal (t - s) := by
  rw [nndist_eq_nnnorm, ← nnnorm_neg, neg_sub]
  exact (Real.toNNReal_eq_nnnorm_of_nonneg (sub_nonneg.mpr hst)).symm

lemma bmCoord_incr_law (B : MultiBrownian Ω P 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasLaw (fun ω => bmCoord B t ω - bmCoord B s ω)
      (gaussianReal 0 (Real.toNNReal (t - s))) P := by
  have hsub :=
    (B.isBrownian ⟨0, Nat.succ_pos 0⟩).toIsPreBrownianReal.hasLaw_sub
      (Real.toNNReal s) (Real.toNNReal t)
  have hcoord :
      (fun ω => bmCoord B t ω - bmCoord B s ω) =
        -((fun ω => B.Wnn (Real.toNNReal s) ω ⟨0, Nat.succ_pos 0⟩) -
          (fun ω => B.Wnn (Real.toNNReal t) ω ⟨0, Nat.succ_pos 0⟩)) := by
    funext ω
    simp only [bmCoord, MultiBrownian.W, reindexProcessFin, toNNRealTime,
      Pi.neg_apply, Pi.sub_apply]
    ring
  have hnnd : nndist ((Real.toNNReal s : ℝ)) ((Real.toNNReal t : ℝ)) =
      Real.toNNReal (t - s) := by
    rw [Real.coe_toNNReal s hs, Real.coe_toNNReal t (hs.trans hst), nndist_of_le hst]
  rw [hcoord]
  convert gaussianReal_neg hsub
  · rw [neg_zero]
  · exact hnnd.symm

/-- Standardized grid increments are standard normal. -/
lemma stdIncr_law (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    HasLaw (stdIncr (bmCoord B) T n) (gaussianReal 0 1) P := by
  have h1 := bmCoord_incr_law B (tGrid_mem hT n).1 (tGrid_lt_succ hT n).le
  rw [tGrid_succ_sub] at h1
  have hdiv := gaussianReal_div_const h1 (Real.sqrt (dtGrid T n))
  have heq :
      (fun ω =>
          (bmCoord B (tGrid T (n + 1)) ω - bmCoord B (tGrid T n) ω) /
            Real.sqrt (dtGrid T n)) = stdIncr (bmCoord B) T n :=
    rfl
  rw [heq] at hdiv
  have hmean : (0 : ℝ) / Real.sqrt (dtGrid T n) = 0 := by simp
  have hsq : (Real.sqrt (dtGrid T n)) ^ 2 = dtGrid T n :=
    Real.sq_sqrt (dtGrid_pos hT n).le
  have hmk : NNReal.mk ((Real.sqrt (dtGrid T n)) ^ 2) (sq_nonneg _) =
      (dtGrid T n).toNNReal := by
    refine Subtype.ext ?_
    simp [hsq, Real.coe_toNNReal _ (dtGrid_pos hT n).le]
  have hvar :
      (dtGrid T n).toNNReal /
        NNReal.mk ((Real.sqrt (dtGrid T n)) ^ 2) (sq_nonneg _) = 1 := by
    rw [hmk, div_self]
    exact (Real.toNNReal_pos.mpr (dtGrid_pos hT n)).ne'
  rw [hmean, hvar] at hdiv
  exact hdiv

/-- Non-hitting prefix events `E_n`: no threshold hit on any of the first `n` grid intervals. -/
def nonHitPrefix (B : ℝ → Ω → ℝ) (T : ℝ) : ℕ → Set Ω
  | 0 => Set.univ
  | n + 1 => nonHitPrefix B T n ∩ noHitEvent B T n


/-- Increments of `bmCoord` after time `s` are independent of the path filtration at `s`. -/
lemma bmCoord_incr_indep (B : MultiBrownian Ω P 1) {s T : ℝ} (hs : 0 ≤ s) (_hsT : s ≤ T) :
    Indep
      (MeasurableSpace.comap
        (fun ω (u : {u : ℝ // s ≤ u ∧ u ≤ T}) => bmCoord B u.1 ω - bmCoord B s ω)
        MeasurableSpace.pi)
      ((pathFiltration B).σAlg s) P := by
  have hshift :=
    (B.isBrownian ⟨0, Nat.succ_pos 0⟩).toIsPreBrownianReal.indepFun_shift (Real.toNNReal s)
  rw [IndepFun_iff_Indep] at hshift
  -- `hshift`: Indep (comap φ π) (comap past π) P, with
  --   φ ω t = Wnn (s.toNNReal + t) ω 0 - Wnn s.toNNReal ω 0, t : ℝ≥0
  --   past ω t = Wnn t.1 ω 0, t : Iic s.toNNReal
  refine indep_of_indep_of_le hshift ?hfut ?hpast
  · -- The `[s, T]` increment map factors through the Mathlib shift process `φ`.
    set φ : Ω → (ℝ≥0 → ℝ) := fun ω t =>
      B.Wnn (Real.toNNReal s + t) ω ⟨0, Nat.succ_pos 0⟩ -
        B.Wnn (Real.toNNReal s) ω ⟨0, Nat.succ_pos 0⟩
    set f : (ℝ≥0 → ℝ) → ({u : ℝ // s ≤ u ∧ u ≤ T} → ℝ) := fun g u =>
      g (Real.toNNReal (u.1 - s))
    have hψ :
        (fun ω (u : {u : ℝ // s ≤ u ∧ u ≤ T}) => bmCoord B u.1 ω - bmCoord B s ω) =
          f ∘ φ := by
      funext ω u
      have hus : 0 ≤ u.1 - s := sub_nonneg.mpr u.2.1
      have hsum : Real.toNNReal s + Real.toNNReal (u.1 - s) = Real.toNNReal u.1 := by
        rw [← Real.toNNReal_add hs hus, add_sub_cancel]
      change
        B.Wnn (toNNRealTime u.1) ω ⟨0, Nat.succ_pos 0⟩ -
            B.Wnn (toNNRealTime s) ω ⟨0, Nat.succ_pos 0⟩ =
          φ ω (Real.toNNReal (u.1 - s))
      simp only [φ, toNNRealTime, hsum]
    have hf : Measurable f :=
      measurable_pi_iff.mpr fun u => measurable_pi_apply _
    rw [hψ, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  · refine iSup_le fun u => iSup_le fun i => ?_
    have hi : i = ⟨0, Nat.succ_pos 0⟩ := Subsingleton.elim _ _
    have hu : Real.toNNReal u.1 ∈ Set.Iic (Real.toNNReal s) := by
      simpa [Set.mem_Iic, Real.toNNReal_le_toNNReal_iff hs] using u.2.2
    have hgen :
        ((fun (v : ℝ) (j : Fin 1) (ω : Ω) => MultiBrownian.W B v ω j) u.1 i) =
          fun ω => MultiBrownian.W B u.1 ω i :=
      rfl
    have heq : (fun ω => MultiBrownian.W B u.1 ω i) =
        (fun (g : Set.Iic (Real.toNNReal s) → ℝ) => g ⟨Real.toNNReal u.1, hu⟩) ∘
          (fun ω (t : Set.Iic (Real.toNNReal s)) =>
            B.Wnn t.1 ω ⟨0, Nat.succ_pos 0⟩) := by
      funext ω
      simp [hi, MultiBrownian.W, reindexProcessFin, toNNRealTime]
    rw [hgen, heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le


/-- `noHitEvent` is measurable in the increment σ-algebra after `t_n` (hence independent of
the path filtration at `t_n`), measurable in `ℱ_{t_{n+1}}`, and contained in `{Z_n < 1}`. -/
lemma noHitEvent_props (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    MeasurableSet[(pathFiltration B).σAlg (tGrid T (n + 1))]
      (noHitEvent (bmCoord B) T n) ∧
    (∀ F : Set Ω, MeasurableSet[(pathFiltration B).σAlg (tGrid T n)] F →
      P (F ∩ noHitEvent (bmCoord B) T n) = P F * P (noHitEvent (bmCoord B) T n)) ∧
    noHitEvent (bmCoord B) T n ⊆ {ω | stdIncr (bmCoord B) T n ω < 1} := by
  set a := tGrid T n
  set b := tGrid T (n + 1)
  set c := Real.sqrt (dtGrid T n)
  have haT : a ≤ T := (tGrid_mem hT n).2
  have hbT : b ≤ T := (tGrid_mem hT (n + 1)).2
  have hab0 : Icc a b ⊆ Ici (0 : ℝ) := fun t ht => (tGrid_mem hT n).1.trans ht.1
  have hcompl_eq : (noHitEvent (bmCoord B) T n)ᶜ =
      ⋂ k : ℕ, (⋃ q : ℚ, if a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b then
        {ω | c - 1 / ((k : ℝ) + 1) < bmCoord B q ω - bmCoord B a ω} else ∅) ∪
        {ω | c ≤ bmCoord B b ω - bmCoord B a ω} := by
    ext ω
    have hneg : ω ∈ (noHitEvent (bmCoord B) T n)ᶜ ↔
        ∃ s ∈ Icc a b, c ≤ bmCoord B s ω - bmCoord B a ω := by
      simp only [noHitEvent, a, b, c, mem_compl_iff, mem_ofPred, not_forall, not_lt, mem_Icc]
      constructor
      · rintro ⟨s, ⟨hs1, hs2⟩, hsc⟩; exact ⟨s, ⟨hs1, hs2⟩, hsc⟩
      · rintro ⟨s, ⟨hs1, hs2⟩, hsc⟩; exact ⟨s, ⟨hs1, hs2⟩, hsc⟩
    have hf : ContinuousOn (fun u => bmCoord B u ω - bmCoord B a ω) (Icc a b) :=
      ((bmCoord_cont B ω).mono hab0).sub continuousOn_const
    rw [hneg, exists_hit_iff_rat (tGrid_lt_succ hT n).le hf]
    simp only [Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
    refine forall_congr' fun k => or_congr_left (exists_congr fun q => ?_)
    by_cases hq : a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b
    · simp [a, b, hq]
    · simp only [ite_eq_right hq, mem_empty_iff_false, a, b]
      constructor
      · intro h
        exact hq ⟨h.1, h.2.1⟩
      · intro h
        exact h.elim
  -- Increment process after `t_n`. Not a `let` of type `MeasurableSpace`, which would
  -- become a local instance and conflict with the ambient space.
  set incrProc : Ω → ({u : ℝ // a ≤ u ∧ u ≤ T} → ℝ) :=
    fun ω u => bmCoord B u.1 ω - bmCoord B a ω
  have hproc :
      Measurable[MeasurableSpace.comap incrProc MeasurableSpace.pi] incrProc :=
    comap_measurable _
  have hlt (u : {u : ℝ // a ≤ u ∧ u ≤ T}) (p : ℝ) :
      MeasurableSet[MeasurableSpace.comap incrProc MeasurableSpace.pi]
        {ω | p < incrProc ω u} := by
    change MeasurableSet[MeasurableSpace.comap incrProc MeasurableSpace.pi]
      (incrProc ⁻¹' {g | p < g u})
    exact hproc (measurableSet_lt measurable_const (measurable_pi_apply u))
  have hle (u : {u : ℝ // a ≤ u ∧ u ≤ T}) (p : ℝ) :
      MeasurableSet[MeasurableSpace.comap incrProc MeasurableSpace.pi]
        {ω | p ≤ incrProc ω u} := by
    change MeasurableSet[MeasurableSpace.comap incrProc MeasurableSpace.pi]
      (incrProc ⁻¹' {g | p ≤ g u})
    exact hproc (measurableSet_le measurable_const (measurable_pi_apply u))
  have hfut : MeasurableSet[MeasurableSpace.comap incrProc MeasurableSpace.pi]
      (noHitEvent (bmCoord B) T n) := by
    refine @MeasurableSet.of_compl Ω (noHitEvent (bmCoord B) T n)
      (MeasurableSpace.comap incrProc MeasurableSpace.pi) ?_
    rw [hcompl_eq]
    refine @MeasurableSet.iInter Ω ℕ (MeasurableSpace.comap incrProc MeasurableSpace.pi) _ _
      (fun k => ?_)
    refine @MeasurableSet.union Ω (MeasurableSpace.comap incrProc MeasurableSpace.pi) _ _ ?_ ?_
    · refine @MeasurableSet.iUnion Ω ℚ (MeasurableSpace.comap incrProc MeasurableSpace.pi) _ _
        (fun q => ?_)
      split_ifs with hq
      · exact hlt ⟨q, hq.1, hq.2.trans hbT⟩ (c - 1 / ((k : ℝ) + 1))
      · exact @MeasurableSet.empty Ω (MeasurableSpace.comap incrProc MeasurableSpace.pi)
    · exact hle ⟨b, (tGrid_lt_succ hT n).le, hbT⟩ c
  have hmeas_b : MeasurableSet[(pathFiltration B).σAlg b]
      (noHitEvent (bmCoord B) T n) := by
    refine @MeasurableSet.of_compl Ω (noHitEvent (bmCoord B) T n)
      ((pathFiltration B).σAlg b) ?_
    rw [hcompl_eq]
    refine @MeasurableSet.iInter Ω ℕ ((pathFiltration B).σAlg b) _ _ (fun k => ?_)
    refine @MeasurableSet.union Ω ((pathFiltration B).σAlg b) _ _ ?_ ?_
    · refine @MeasurableSet.iUnion Ω ℚ ((pathFiltration B).σAlg b) _ _ (fun q => ?_)
      split_ifs with hq
      · have h1 := bmCoord_adapted B ⟨(tGrid_mem hT n).1.trans hq.1, hq.2⟩
        have h2 := bmCoord_adapted B ⟨(tGrid_mem hT n).1, (tGrid_lt_succ hT n).le⟩
        change MeasurableSet[(pathFiltration B).σAlg b]
          ((fun ω => bmCoord B (q : ℝ) ω - bmCoord B a ω) ⁻¹'
            Ioi (c - 1 / ((k : ℝ) + 1)))
        exact (h1.sub h2) measurableSet_Ioi
      · exact @MeasurableSet.empty Ω ((pathFiltration B).σAlg b)
    · have h1 := bmCoord_adapted B ⟨(tGrid_mem hT (n + 1)).1, le_rfl⟩
      have h2 := bmCoord_adapted B ⟨(tGrid_mem hT n).1, (tGrid_lt_succ hT n).le⟩
      change MeasurableSet[(pathFiltration B).σAlg b]
        ((fun ω => bmCoord B b ω - bmCoord B a ω) ⁻¹' Ici c)
      exact (h1.sub h2) measurableSet_Ici
  refine ⟨hmeas_b, fun F hF => ?_, noHitEvent_subset_stdIncr hT _ n⟩
  have hind :=
    (Indep_iff _ _ _).mp
      (bmCoord_incr_indep B (tGrid_mem hT n).1 haT).symm
  exact hind F (noHitEvent (bmCoord B) T n) hF hfut

/-- **Lemma 4.2**: The non-hitting prefixes decay geometrically: `P(E_n) ≤ q^n`,
where `q = P(Z < 1) < 1` for `Z ~ N(0, 1)`, hence `P(⋂ E_n) = 0`. -/
lemma nonHitPrefix_props (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    (∀ n, MeasurableSet[(pathFiltration B).σAlg (tGrid T n)]
      (nonHitPrefix (bmCoord B) T n)) ∧
    (∀ n, P (nonHitPrefix (bmCoord B) T n) ≤
      ((gaussianReal 0 1) (Iio (1 : ℝ))) ^ n) ∧
    P (⋂ n : ℕ, nonHitPrefix (bmCoord B) T n) = 0 := by
  have hmeas : ∀ n, MeasurableSet[(pathFiltration B).σAlg (tGrid T n)]
      (nonHitPrefix (bmCoord B) T n) := by
    intro n; induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
      have hle : ∀ s, MeasurableSet[(pathFiltration B).σAlg (tGrid T n)] s →
          MeasurableSet[(pathFiltration B).σAlg (tGrid T (n + 1))] s :=
        (pathFiltration B).mono (tGrid_lt_succ hT n).le
      exact (hle _ ih).inter (noHitEvent_props B hT n).1
  have hprob : ∀ n, P (nonHitPrefix (bmCoord B) T n) ≤
      ((gaussianReal 0 1) (Iio (1 : ℝ))) ^ n := by
    intro n; induction n with
    | zero => simp [nonHitPrefix]
    | succ n ih =>
      rw [nonHitPrefix, (noHitEvent_props B hT n).2.1 _ (hmeas n), pow_succ]
      have hAn : P (noHitEvent (bmCoord B) T n) ≤ (gaussianReal 0 1) (Iio (1 : ℝ)) := by
        calc P (noHitEvent (bmCoord B) T n)
            ≤ P {ω | stdIncr (bmCoord B) T n ω < 1} :=
              measure_mono (noHitEvent_props B hT n).2.2
          _ = (gaussianReal 0 1) (Iio (1 : ℝ)) := by
              rw [← (stdIncr_law B hT n).map_eq,
                Measure.map_apply_of_aemeasurable
                  (stdIncr_law B hT n).aemeasurable measurableSet_Iio]
              rfl
      exact mul_le_mul' ih hAn
  refine ⟨hmeas, hprob, ?_⟩
  refine le_antisymm ?_ bot_le
  have hlim : Tendsto (fun n : ℕ => ((gaussianReal 0 1) (Iio (1 : ℝ))) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one gaussian_Iio_one_lt_one
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun n =>
    (measure_mono (Set.iInter_subset (nonHitPrefix (bmCoord B) T) n)).trans (hprob n))


/-- Recursive doubling wealth `X_n` at the grid time `t_n`. -/
def doublingX (B : ℝ → Ω → ℝ) (T : ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω =>
    let c := (1 - doublingX B T n ω) / Real.sqrt (dtGrid T n)
    doublingX B T n ω +
      (if ω ∈ nonHitPrefix B T n then c * (B (tauHit B T n ω) ω - B (tGrid T n) ω) else 0)

/-- Position on the nth grid interval: `c_n = (1 - X_n) / √(Δt_n)`. -/
def doublingC (B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1 - doublingX B T n ω) / Real.sqrt (dtGrid T n)

/-- Exact closed form on `E_n` and exact value `1` on `E_nᶜ`. -/
lemma doublingX_closed_form (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ n ω,
      (ω ∈ nonHitPrefix (bmCoord B) T n →
        1 - doublingX (bmCoord B) T n ω =
          ∏ j ∈ Finset.range n, (1 - stdIncr (bmCoord B) T j ω)) ∧
      (ω ∉ nonHitPrefix (bmCoord B) T n → doublingX (bmCoord B) T n ω = 1)
  | 0, ω => ⟨fun _ => by simp [doublingX], fun h => absurd (Set.mem_univ ω) h⟩
  | n + 1, ω => by
    obtain ⟨ihE, ihEc⟩ := doublingX_closed_form B hT n ω
    constructor
    · intro hEn1
      have hEn : ω ∈ nonHitPrefix (bmCoord B) T n := hEn1.1
      have hAn : ω ∈ noHitEvent (bmCoord B) T n := hEn1.2
      have htau : tauHit (bmCoord B) T n ω = tGrid T (n + 1) :=
        ((tauHit_spec B hT n ω).1 hAn).1
      simp only [doublingX, hEn, ite_true, htau, Finset.prod_range_succ, ← ihE hEn]
      have hZ :
          (1 - doublingX (bmCoord B) T n ω) / Real.sqrt (dtGrid T n) *
            (bmCoord B (tGrid T (n + 1)) ω - bmCoord B (tGrid T n) ω) =
          (1 - doublingX (bmCoord B) T n ω) * stdIncr (bmCoord B) T n ω := by
        simp only [stdIncr]; ring
      rw [hZ]; ring
    · intro hnEn1
      by_cases hEn : ω ∈ nonHitPrefix (bmCoord B) T n
      · have hnAn : ω ∉ noHitEvent (bmCoord B) T n := fun hAn => hnEn1 ⟨hEn, hAn⟩
        have hhit := (tauHit_spec B hT n ω).2 hnAn
        have hsq : Real.sqrt (dtGrid T n) ≠ 0 := (Real.sqrt_pos.mpr (dtGrid_pos hT n)).ne'
        simp only [doublingX, hEn, ite_true, hhit]
        field_simp [hsq]
        ring
      · simp only [doublingX, hEn, ite_false, add_zero]
        exact ihEc hEn

/-- Almost every path hits the threshold on some grid interval, after which wealth stays at `1`.
Hence `X_n → 1` almost surely (and `X_n = 1` for all large `n`). -/
lemma doublingX_eq_one_eventually (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, doublingX (bmCoord B) T n ω = 1 := by
  have hnull : P (⋂ n, nonHitPrefix (bmCoord B) T n) = 0 := (nonHitPrefix_props B hT).2.2
  refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun ω hω => ?_
  have hex : ∃ N, ω ∉ nonHitPrefix (bmCoord B) T N := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hω (mem_iInter.mpr h)
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ?_⟩
  have hnot : ω ∉ nonHitPrefix (bmCoord B) T n := by
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ k hk ih =>
      intro hmem
      exact ih hmem.1
  exact (doublingX_closed_form B hT n ω).2 hnot

/-- Terminal doubling wealth: `1` off the null set `⋂ E_n`. -/
def doublingVT (B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  if ω ∈ ⋂ n, nonHitPrefix B T n then 0 else 1

lemma doublingVT_eq_one_ae (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    doublingVT (bmCoord B) T =ᵐ[P] fun _ => (1 : ℝ) := by
  have hnull : P (⋂ n, nonHitPrefix (bmCoord B) T n) = 0 := (nonHitPrefix_props B hT).2.2
  refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun ω hω => ?_
  simp [doublingVT, hω]


lemma tGrid_tendsto (T : ℝ) : Tendsto (fun n : ℕ => tGrid T n) atTop (𝓝 T) := by
  have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
  have hmul : Tendsto (fun n : ℕ => T * (1 - (1 / 2 : ℝ) ^ n)) atTop (𝓝 (T * (1 - 0))) :=
    (tendsto_const_nhds (x := T)).mul hone
  simpa [tGrid] using hmul

lemma exists_tGrid_ge {T s : ℝ} (hT : 0 < T) (hs : s < T) :
    ∃ n : ℕ, s ≤ tGrid T (n + 1) := by
  obtain ⟨n, hn⟩ := ((tendsto_order.1 (tGrid_tendsto T)).1 s hs).exists
  cases n with
  | zero =>
    refine ⟨0, le_of_lt (hn.trans ?_)⟩
    simp [tGrid, hT]
    linarith
  | succ k =>
    exact ⟨k, hn.le⟩

/-- The unique grid index with `t_n < s ≤ t_{n+1}` when `s ∈ (0, T)`; `0` otherwise. -/
def nGrid (T s : ℝ) : ℕ :=
  if h : 0 < T ∧ s < T then Nat.find (exists_tGrid_ge h.1 h.2) else 0

lemma nGrid_spec {T s : ℝ} (hT : 0 < T) (hs0 : 0 < s) (hsT : s < T) :
    tGrid T (nGrid T s) < s ∧ s ≤ tGrid T (nGrid T s + 1) := by
  have hfind := Nat.find_spec (exists_tGrid_ge hT hsT)
  have hn : nGrid T s = Nat.find (exists_tGrid_ge hT hsT) := by
    simp [nGrid, hT, hsT]
  rw [hn]
  refine ⟨?_, hfind⟩
  cases hfn : Nat.find (exists_tGrid_ge hT hsT) with
  | zero =>
    simp only [tGrid_zero]
    exact hs0
  | succ n =>
    have hlt : ¬ s ≤ tGrid T (n + 1) :=
      Nat.find_min (exists_tGrid_ge hT hsT) (by rw [hfn]; exact Nat.lt_succ_self n)
    exact lt_of_not_ge hlt

/-- Geometric-grid doubling integrand `K` (Carbon): on the nth interval it takes the
constant position `c_n` up to the hitting time `τ_n`, provided the path has not already
hit, and `0` elsewhere. -/
def doublingK (B : ℝ → Ω → ℝ) (T : ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ∑' n : ℕ, if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
    then doublingC B T n ω else 0

/-- `L²`-localizing times `σ_N = t_N` on `E_N` and `T` after the first hit. -/
def doublingSigma (B : ℝ → Ω → ℝ) (T : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  if ω ∈ nonHitPrefix B T N then tGrid T N else T

/-- A `[0, T]`-valued stopping time of the filtration `σAlg`. -/
def IsStoppingTimeOn {Ω : Type*} [MeasurableSpace Ω]
    (σAlg : ℝ → MeasurableSpace Ω) (T : ℝ) (τ : Ω → ℝ) : Prop :=
  (∀ ω, τ ω ∈ Icc 0 T) ∧
    ∀ t, t ∈ Icc 0 T → MeasurableSet[σAlg t] {ω | τ ω ≤ t}

lemma isStoppingTime_doublingSigma (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (N : ℕ) :
    IsStoppingTimeOn (pathFiltration B).σAlg T (doublingSigma (bmCoord B) T N) := by
  refine ⟨fun ω => ?_, fun t ht => ?_⟩
  · simp only [doublingSigma]
    by_cases hE : ω ∈ nonHitPrefix (bmCoord B) T N
    · simpa [hE] using tGrid_mem hT N
    · simp [hE, hT.le]
  · by_cases htT : t = T
    · have : {ω | doublingSigma (bmCoord B) T N ω ≤ t} = Set.univ :=
        Set.eq_univ_iff_forall.mpr fun ω => by
          simp only [doublingSigma]
          by_cases hE : ω ∈ nonHitPrefix (bmCoord B) T N
          · simpa [hE] using (tGrid_mem hT N).2.trans htT.ge
          · simp [hE, htT.ge]
      rw [this]
      exact @MeasurableSet.univ Ω ((pathFiltration B).σAlg t)
    have ht_lt : t < T := lt_of_le_of_ne ht.2 htT
    by_cases htN : t < tGrid T N
    · have : {ω | doublingSigma (bmCoord B) T N ω ≤ t} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun ω hω => by
          simp only [doublingSigma] at hω
          by_cases hE : ω ∈ nonHitPrefix (bmCoord B) T N
          · simp [hE] at hω
            exact (not_le.mpr htN) hω
          · simp [hE] at hω
            exact (not_le.mpr ht_lt) hω
      rw [this]
      exact @MeasurableSet.empty Ω ((pathFiltration B).σAlg t)
    have hge : tGrid T N ≤ t := le_of_not_gt htN
    have heq : {ω | doublingSigma (bmCoord B) T N ω ≤ t} =
        nonHitPrefix (bmCoord B) T N := by
      ext ω
      simp only [doublingSigma]
      by_cases hE : ω ∈ nonHitPrefix (bmCoord B) T N
      · simp [hE, hge]
      · simp [hE, not_le.mpr ht_lt]
    rw [heq]
    exact ((pathFiltration B).mono hge) _ ((nonHitPrefix_props B hT).1 N)

/-- On `⋃ N, E_Nᶜ` (probability 1), `doublingK` vanishes after `t_{N(ω)}`, hence
`∫₀ᵀ K_s² ds < ∞` a.s. -/
lemma doublingK_sq_int_finite_ae (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∫⁻ s in Icc 0 T, ENNReal.ofReal (doublingK (bmCoord B) T s ω ^ 2) ∂volume < ⊤ := by
  have hhit : ∀ᵐ ω ∂P, ∃ N : ℕ, ω ∉ nonHitPrefix (bmCoord B) T N := by
    have h0 := (nonHitPrefix_props B hT).2.2
    refine (measure_eq_zero_iff_ae_notMem.mp h0).mono fun ω hω => ?_
    simpa [mem_iInter] using hω
  filter_upwards [hhit] with ω ⟨N, hN⟩
  have hvan : ∀ n ≥ N, ω ∉ nonHitPrefix (bmCoord B) T n := by
    intro n hn
    induction hn with
    | refl => exact hN
    | step _ ih => exact fun h => ih h.1
  set C : ℝ := ∑ n ∈ Finset.range N, |doublingC (bmCoord B) T n ω|
  have hK_le : ∀ s : ℝ, |doublingK (bmCoord B) T s ω| ≤ C := fun s => by
    have htsum : doublingK (bmCoord B) T s ω =
        ∑ n ∈ Finset.range N,
          if ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
              s ≤ tauHit (bmCoord B) T n ω
            then doublingC (bmCoord B) T n ω else 0 :=
      tsum_eq_sum fun n hn => by
        have hge : N ≤ n := by
          simp only [Finset.mem_range, not_lt] at hn
          exact hn
        simp [hvan n hge]
    rw [htsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    split_ifs
    · exact le_rfl
    · rw [abs_zero]; exact abs_nonneg _
  calc ∫⁻ s in Icc 0 T, ENNReal.ofReal (doublingK (bmCoord B) T s ω ^ 2) ∂volume
      ≤ ∫⁻ _s in Icc 0 T, ENNReal.ofReal (C ^ 2) ∂volume :=
        setLIntegral_mono' measurableSet_Icc fun s _ =>
          ENNReal.ofReal_le_ofReal (by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hK_le s) 2)
    _ = ENNReal.ofReal (C ^ 2) * volume (Icc 0 T) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

end SignatureVolatility
