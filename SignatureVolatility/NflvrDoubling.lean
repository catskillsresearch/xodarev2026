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

end SignatureVolatility
