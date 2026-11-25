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


lemma isStoppingTime_tauHit (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    IsStoppingTimeOn (pathFiltration B).σAlg T (tauHit (bmCoord B) T n) := by
  refine ⟨fun ω =>
    ⟨(tGrid_mem hT n).1.trans (tauHit_mem_Icc hT (bmCoord B) n ω).1,
      (tauHit_mem_Icc hT (bmCoord B) n ω).2.trans (tGrid_mem hT (n + 1)).2⟩,
    fun t ht => ?_⟩
  set a := tGrid T n
  set b := tGrid T (n + 1)
  set c := Real.sqrt (dtGrid T n)
  by_cases hta : t < a
  · have : {ω | tauHit (bmCoord B) T n ω ≤ t} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun ω hω =>
        not_lt.mpr ((tauHit_mem_Icc hT (bmCoord B) n ω).1.trans hω) hta
    rw [this]
    exact @MeasurableSet.empty Ω ((pathFiltration B).σAlg t)
  by_cases htb : b ≤ t
  · have : {ω | tauHit (bmCoord B) T n ω ≤ t} = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun ω =>
        (tauHit_mem_Icc hT (bmCoord B) n ω).2.trans htb
    rw [this]
    exact @MeasurableSet.univ Ω ((pathFiltration B).σAlg t)
  have hat : a ≤ t := le_of_not_gt hta
  have htltb : t < b := lt_of_not_ge htb
  have hiff : ∀ ω, tauHit (bmCoord B) T n ω ≤ t ↔
      ∃ s ∈ Icc a t, c ≤ bmCoord B s ω - bmCoord B a ω := fun ω => by
    constructor
    · intro hle
      have hnA : ω ∉ noHitEvent (bmCoord B) T n := fun hA => by
        have htau := ((tauHit_spec B hT n ω).1 hA).1
        linarith
      exact ⟨tauHit (bmCoord B) T n ω,
        ⟨(tauHit_mem_Icc hT (bmCoord B) n ω).1, hle⟩,
        ((tauHit_spec B hT n ω).2 hnA).ge⟩
    · rintro ⟨s, hs, hcs⟩
      have hsI : s ∈ Icc a b := ⟨hs.1, hs.2.trans htltb.le⟩
      have hS : (hitSet (bmCoord B) T n ω).Nonempty := ⟨s, hsI, hcs⟩
      have htau : tauHit (bmCoord B) T n ω = sInf (hitSet (bmCoord B) T n ω) := by
        simp [tauHit, hS]
      rw [htau]
      have hlb : BddBelow (hitSet (bmCoord B) T n ω) :=
        ⟨a, fun u hu => (mem_Icc.mp hu.1).1⟩
      exact (csInf_le hlb ⟨hsI, hcs⟩).trans hs.2
  have hab0 : Icc a t ⊆ Ici (0 : ℝ) := fun u hu => (tGrid_mem hT n).1.trans hu.1
  have hset : {ω | tauHit (bmCoord B) T n ω ≤ t} =
      ⋂ k : ℕ, (⋃ q : ℚ, if a ≤ (q : ℝ) ∧ (q : ℝ) ≤ t then
        {ω | c - 1 / ((k : ℝ) + 1) < bmCoord B q ω - bmCoord B a ω} else ∅) ∪
        {ω | c ≤ bmCoord B t ω - bmCoord B a ω} := by
    ext ω
    have hf : ContinuousOn (fun u => bmCoord B u ω - bmCoord B a ω) (Icc a t) :=
      ((bmCoord_cont B ω).mono hab0).sub continuousOn_const
    simp only [Set.mem_ofPred_eq]
    rw [hiff ω, exists_hit_iff_rat hat hf]
    simp only [Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
    refine forall_congr' fun k => or_congr_left (exists_congr fun q => ?_)
    by_cases hq : a ≤ (q : ℝ) ∧ (q : ℝ) ≤ t
    · simp [hq]
    · simp only [ite_eq_right hq, mem_empty_iff_false]
      constructor
      · intro h
        exact hq ⟨h.1, h.2.1⟩
      · intro h
        exact h.elim
  rw [hset]
  refine @MeasurableSet.iInter Ω ℕ ((pathFiltration B).σAlg t) _ _ (fun k => ?_)
  refine @MeasurableSet.union Ω ((pathFiltration B).σAlg t) _ _ ?_ ?_
  · refine @MeasurableSet.iUnion Ω ℚ ((pathFiltration B).σAlg t) _ _ (fun q => ?_)
    split_ifs with hq
    · have h1 := bmCoord_adapted (T := t) B ⟨(tGrid_mem hT n).1.trans hq.1, hq.2⟩
      have h2 := bmCoord_adapted (T := t) B ⟨(tGrid_mem hT n).1, hat⟩
      change MeasurableSet[(pathFiltration B).σAlg t]
        ((fun ω => bmCoord B (q : ℝ) ω - bmCoord B a ω) ⁻¹'
          Ioi (c - 1 / ((k : ℝ) + 1)))
      exact (h1.sub h2) measurableSet_Ioi
    · exact @MeasurableSet.empty Ω ((pathFiltration B).σAlg t)
  · have h1 := bmCoord_adapted (T := t) B ⟨ht.1, le_rfl⟩
    have h2 := bmCoord_adapted (T := t) B ⟨(tGrid_mem hT n).1, hat⟩
    change MeasurableSet[(pathFiltration B).σAlg t]
      ((fun ω => bmCoord B t ω - bmCoord B a ω) ⁻¹' Ici c)
    exact (h1.sub h2) measurableSet_Ici


lemma tGrid_mono {T : ℝ} (hT : 0 < T) : Monotone (tGrid T) :=
  (strictMono_nat_of_lt_succ fun n => tGrid_lt_succ hT n).monotone

lemma measurable_stdIncr (B : MultiBrownian Ω P 1) {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    Measurable (stdIncr (bmCoord B) T n) :=
  ((bmCoord_meas B (tGrid T (n + 1))).sub (bmCoord_meas B (tGrid T n))).div_const _

/-- `∫ (1 - Z)² dγ = 2` for `Z ~ N(0,1)`. -/
lemma integral_one_sub_stdIncr_sq (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((1 - stdIncr (bmCoord B) T m ω) ^ 2) ∂P = ENNReal.ofReal 2 := by
  have hlaw := stdIncr_law B hT m
  have hi : Integrable (fun x : ℝ => (1 - x) ^ 2) (gaussianReal 0 1) :=
    ((memLp_const (1 : ℝ)).sub (memLp_id_gaussianReal' 2 (by simp))).integrable_sq
  have hsq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hvar :=
      variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id)
        aemeasurable_id' integral_id_gaussianReal
    simpa [variance_id_gaussianReal, id] using hvar.symm
  have hval : ∫ x : ℝ, (1 - x) ^ 2 ∂(gaussianReal 0 1) = 2 := by
    have hexp : (fun x : ℝ => (1 - x) ^ 2) = fun x => (1 : ℝ) - 2 * x + x ^ 2 :=
      funext fun x => by ring
    have hi1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
    have hi2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
    have hf : Integrable (fun x : ℝ => (1 : ℝ) - 2 * x) (gaussianReal 0 1) := by
      have h := (integrable_const (1 : ℝ)).sub (hi1.const_mul 2)
      have heq : ((fun _ : ℝ => (1 : ℝ)) - fun x => (2 : ℝ) * x) =
          fun x => (1 : ℝ) - 2 * x :=
        funext fun x => by simp [Pi.sub_apply]
      rwa [heq] at h
    rw [hexp]
    change (∫ x : ℝ, ((fun y : ℝ => (1 : ℝ) - 2 * y) x + (fun y : ℝ => y ^ 2) x)
      ∂(gaussianReal 0 1)) = 2
    rw [integral_add hf hi2, integral_sub (integrable_const (1 : ℝ)) (hi1.const_mul 2),
      integral_const_mul, integral_id_gaussianReal, integral_const, probReal_univ,
      one_smul, hsq]
    ring
  have hmap :
      (∫⁻ x, ENNReal.ofReal ((1 - x) ^ 2) ∂Measure.map (stdIncr (bmCoord B) T m) P) =
        ∫⁻ ω, ENNReal.ofReal ((1 - stdIncr (bmCoord B) T m ω) ^ 2) ∂P :=
    lintegral_map
      (f := fun x : ℝ => ENNReal.ofReal ((1 - x) ^ 2))
      (g := stdIncr (bmCoord B) T m)
      (ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).pow_const 2))
      (measurable_stdIncr B hT m)
  rw [← hmap, hlaw.map_eq, ← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun _ => sq_nonneg _), hval]


/-- The product second-moment identity `𝔼[∏_{j<m} (1-Z_j)²] = 2^m`. -/
lemma lintegral_prod_one_sub_stdIncr_sq (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ m : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (∏ j ∈ Finset.range m, (1 - stdIncr (bmCoord B) T j ω) ^ 2) ∂P =
        ENNReal.ofReal ((2 : ℝ) ^ m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    simp_rw [Finset.prod_range_succ,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => sq_nonneg _)]
    have hm1 : Measurable[(pathFiltration B).σAlg (tGrid T m)]
        (fun ω => ∏ j ∈ Finset.range m, (1 - stdIncr (bmCoord B) T j ω) ^ 2) := by
      refine Finset.measurable_prod _ fun j hj => ?_
      have hjm : j < m := Finset.mem_range.mp hj
      have hle1 : tGrid T (j + 1) ≤ tGrid T m := tGrid_mono hT (Nat.succ_le_of_lt hjm)
      have hle0 : tGrid T j ≤ tGrid T m := (tGrid_lt_succ hT j).le.trans hle1
      have hB1 := bmCoord_adapted (T := tGrid T m) B
        ⟨(tGrid_mem hT (j + 1)).1, hle1⟩
      have hB0 := bmCoord_adapted (T := tGrid T m) B
        ⟨(tGrid_mem hT j).1, hle0⟩
      exact (measurable_const.sub ((hB1.sub hB0).div_const _)).pow_const 2
    set incrProc : Ω → ({u : ℝ // tGrid T m ≤ u ∧ u ≤ T} → ℝ) :=
      fun ω u => bmCoord B u.1 ω - bmCoord B (tGrid T m) ω
    have hZ_fut : Measurable[MeasurableSpace.comap incrProc MeasurableSpace.pi]
        (fun ω => ENNReal.ofReal ((1 - stdIncr (bmCoord B) T m ω) ^ 2)) := by
      have hu : tGrid T m ≤ tGrid T (m + 1) ∧ tGrid T (m + 1) ≤ T :=
        ⟨(tGrid_lt_succ hT m).le, (tGrid_mem hT (m + 1)).2⟩
      have hinc : Measurable[MeasurableSpace.comap incrProc MeasurableSpace.pi]
          (fun ω => incrProc ω ⟨tGrid T (m + 1), hu⟩) :=
        (measurable_pi_apply
          (⟨tGrid T (m + 1), hu⟩ : {u : ℝ // tGrid T m ≤ u ∧ u ≤ T})).comp
          (comap_measurable incrProc)
      exact ((measurable_const.sub (hinc.div_const _)).pow_const 2).ennreal_ofReal
    have hind : IndepFun
        (fun ω => ENNReal.ofReal
          (∏ j ∈ Finset.range m, (1 - stdIncr (bmCoord B) T j ω) ^ 2))
        (fun ω => ENNReal.ofReal ((1 - stdIncr (bmCoord B) T m ω) ^ 2)) P := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le
        (bmCoord_incr_indep B (tGrid_mem hT m).1 (tGrid_mem hT m).2)
        hZ_fut.comap_le (hm1.ennreal_ofReal).comap_le).symm
    have hf : Measurable
        (fun ω => ENNReal.ofReal
          (∏ j ∈ Finset.range m, (1 - stdIncr (bmCoord B) T j ω) ^ 2)) :=
      (hm1.mono ((pathFiltration B).le_ambient (tGrid T m)) le_rfl).ennreal_ofReal
    have hg : Measurable
        (fun ω => ENNReal.ofReal ((1 - stdIncr (bmCoord B) T m ω) ^ 2)) :=
      ((measurable_const.sub (measurable_stdIncr B hT m)).pow_const 2).ennreal_ofReal
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hf hg hind
    simp only [Pi.mul_apply] at hmul
    rw [hmul, ih, integral_one_sub_stdIncr_sq B hT m,
      ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), pow_succ]

/-- Exact `L²` bound `𝔼[(1_{E_n} c_n)²] ≤ 2^n / Δt_n`. -/
lemma doublingC_sq_integral_le (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        ((if ω ∈ nonHitPrefix (bmCoord B) T n then doublingC (bmCoord B) T n ω else 0) ^ 2) ∂P ≤
      ENNReal.ofReal ((2 : ℝ) ^ n / dtGrid T n) := by
  have hpt : ∀ ω,
      ENNReal.ofReal
          ((if ω ∈ nonHitPrefix (bmCoord B) T n then doublingC (bmCoord B) T n ω else 0) ^ 2) ≤
        ENNReal.ofReal ((dtGrid T n)⁻¹) *
          ENNReal.ofReal (∏ j ∈ Finset.range n, (1 - stdIncr (bmCoord B) T j ω) ^ 2) := fun ω => by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (dtGrid_pos hT n).le)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hEn : ω ∈ nonHitPrefix (bmCoord B) T n
    · have hform := (doublingX_closed_form B hT n ω).1 hEn
      have hpos : 0 < dtGrid T n := dtGrid_pos hT n
      simp only [hEn, ite_true, doublingC]
      rw [div_pow, Real.sq_sqrt hpos.le, hform, Finset.prod_pow, div_eq_inv_mul]
    · simp only [hEn, ite_false]
      rw [zero_pow (by exact two_ne_zero)]
      exact mul_nonneg (inv_nonneg.mpr (dtGrid_pos hT n).le)
        (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  have hmeas : Measurable
      (fun ω => ∏ j ∈ Finset.range n, (1 - stdIncr (bmCoord B) T j ω) ^ 2) :=
    Finset.measurable_prod _ fun j _ =>
      (measurable_const.sub (measurable_stdIncr B hT j)).pow_const 2
  calc ∫⁻ ω, ENNReal.ofReal
        ((if ω ∈ nonHitPrefix (bmCoord B) T n then doublingC (bmCoord B) T n ω else 0) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((dtGrid T n)⁻¹) *
          ENNReal.ofReal (∏ j ∈ Finset.range n, (1 - stdIncr (bmCoord B) T j ω) ^ 2) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((dtGrid T n)⁻¹) * ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [lintegral_const_mul _ hmeas.ennreal_ofReal,
          lintegral_prod_one_sub_stdIncr_sq B hT n]
    _ = ENNReal.ofReal ((2 : ℝ) ^ n / dtGrid T n) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (dtGrid_pos hT n).le), div_eq_inv_mul]


/-- Pathwise doubling wealth at time `t`: the stochastic integral of `doublingK` against
`B`, written as an explicit finite-on-almost-every-path sum of stopped increments. -/
def doublingWealth (B : ℝ → Ω → ℝ) (T t : ℝ) (ω : Ω) : ℝ :=
  ∑' n : ℕ, if ω ∈ nonHitPrefix B T n ∧ tGrid T n < t
    then doublingC B T n ω * (B (min t (tauHit B T n ω)) ω - B (tGrid T n) ω)
    else 0

lemma doublingWealth_zero {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (ω : Ω) :
    doublingWealth B T 0 ω = 0 := by
  unfold doublingWealth
  have hterm :
      (fun n : ℕ => if ω ∈ nonHitPrefix B T n ∧ tGrid T n < (0 : ℝ)
        then doublingC B T n ω * (B (min (0 : ℝ) (tauHit B T n ω)) ω - B (tGrid T n) ω)
        else 0) = fun _ => 0 :=
    funext fun n => by
      have hn : ¬ tGrid T n < (0 : ℝ) := not_lt.mpr (tGrid_mem hT n).1
      simp [hn]
  rw [hterm, tsum_zero]

/-- The recursive grid wealth is the sum of the stopped increments up to `N`. -/
lemma doublingX_eq_sum (B : ℝ → Ω → ℝ) (T : ℝ) :
    ∀ N ω, doublingX B T N ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix B T n then
          doublingC B T n ω * (B (tauHit B T n ω) ω - B (tGrid T n) ω) else 0) := by
  intro N ω
  induction N with
  | zero => simp [doublingX]
  | succ N ih =>
    simp [doublingX, Finset.sum_range_succ, ih, doublingC]

/-- After the first hit, later prefixes are empty, so the wealth tsum is a finite sum. -/
lemma doublingWealth_eq_sum {T : ℝ} {N : ℕ} {ω : Ω} (B : ℝ → Ω → ℝ)
    (hN : ω ∉ nonHitPrefix B T N) (t : ℝ) :
    doublingWealth B T t ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < t
          then doublingC B T n ω * (B (min t (tauHit B T n ω)) ω - B (tGrid T n) ω)
          else 0) := by
  have hvan : ∀ n ≥ N, ω ∉ nonHitPrefix B T n := by
    intro n hn
    induction hn with
    | refl => exact hN
    | step _ ih => exact fun h => ih h.1
  exact tsum_eq_sum fun n hn => by
    have hge : N ≤ n := by
      simp only [Finset.mem_range, not_lt] at hn
      exact hn
    simp [hvan n hge]

lemma doublingWealth_T_eq_doublingX {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ)
    {N : ℕ} {ω : Ω} (hN : ω ∉ nonHitPrefix B T N) :
    doublingWealth B T T ω = doublingX B T N ω := by
  rw [doublingWealth_eq_sum (B := B) hN T, doublingX_eq_sum B T N ω]
  refine Finset.sum_congr rfl fun n hn => ?_
  have htlt : tGrid T n < T := tGrid_lt_T hT n
  have hτle : tauHit B T n ω ≤ T :=
    (tauHit_mem_Icc hT B n ω).2.trans (tGrid_mem hT (n + 1)).2
  by_cases hE : ω ∈ nonHitPrefix B T n
  · simp [hE, htlt, min_eq_right hτle]
  · simp [hE]

/-- Almost every path has some first hit, after which grid wealth is `1`, so `V_T = 1` a.s. -/
lemma doublingWealth_T_eq_one_ae (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    (fun ω => doublingWealth (bmCoord B) T T ω) =ᵐ[P] fun _ => (1 : ℝ) := by
  have hhit : ∀ᵐ ω ∂P, ∃ N : ℕ, ω ∉ nonHitPrefix (bmCoord B) T N := by
    have h0 := (nonHitPrefix_props B hT).2.2
    refine (measure_eq_zero_iff_ae_notMem.mp h0).mono fun ω hω => ?_
    simpa [mem_iInter] using hω
  filter_upwards [hhit] with ω ⟨N, hN⟩
  rw [doublingWealth_T_eq_doublingX hT (bmCoord B) hN]
  exact (doublingX_closed_form B hT N ω).2 hN

/-- On `{t_n < t}` the increment starts at `0` at `t = t_n`, so the piece equals the
continuous process `c_n (B_{min (max t t_n) τ_n} - B_{t_n})` (or `0` off `E_n`). -/
lemma doublingWealth_piece_eq {T t : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < t
      then doublingC B T n ω * (B (min t (tauHit B T n ω)) ω - B (tGrid T n) ω)
      else 0) =
      (if ω ∈ nonHitPrefix B T n then
        doublingC B T n ω *
          (B (min (max t (tGrid T n)) (tauHit B T n ω)) ω - B (tGrid T n) ω)
        else 0) := by
  by_cases hE : ω ∈ nonHitPrefix B T n
  · by_cases hlt : tGrid T n < t
    · have hmax : max t (tGrid T n) = t := max_eq_left hlt.le
      simp [hE, hlt, hmax]
    · have hmax : max t (tGrid T n) = tGrid T n := max_eq_right (not_lt.mp hlt)
      have hmin : min (tGrid T n) (tauHit B T n ω) = tGrid T n :=
        min_eq_left (tauHit_mem_Icc hT B n ω).1
      simp [hE, hlt, hmax, hmin]
  · simp [hE]

/-- On almost every path the wealth is a finite sum of continuous stopped increments. -/
lemma doublingWealth_continuousOn_ae (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => doublingWealth (bmCoord B) T t ω) (Icc 0 T) := by
  have hhit : ∀ᵐ ω ∂P, ∃ N : ℕ, ω ∉ nonHitPrefix (bmCoord B) T N := by
    have h0 := (nonHitPrefix_props B hT).2.2
    refine (measure_eq_zero_iff_ae_notMem.mp h0).mono fun ω hω => ?_
    simpa [mem_iInter] using hω
  filter_upwards [hhit] with ω ⟨N, hN⟩
  have hsum : ∀ t, doublingWealth (bmCoord B) T t ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix (bmCoord B) T n then
          doublingC (bmCoord B) T n ω *
            (bmCoord B (min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω)) ω -
              bmCoord B (tGrid T n) ω)
          else 0) := fun t => by
    rw [doublingWealth_eq_sum (B := bmCoord B) hN t]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact doublingWealth_piece_eq hT (bmCoord B) n ω
  set piece : ℕ → ℝ → ℝ := fun n t =>
    if ω ∈ nonHitPrefix (bmCoord B) T n then
      doublingC (bmCoord B) T n ω *
        (bmCoord B (min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω)) ω -
          bmCoord B (tGrid T n) ω)
    else 0
  have hpieces : ∀ n, ContinuousOn (piece n) (Icc 0 T) := fun n => by
    by_cases hE : ω ∈ nonHitPrefix (bmCoord B) T n
    · have hB : ContinuousOn (fun t : ℝ => bmCoord B t ω) (Ici 0) := bmCoord_cont B ω
      have harg : ContinuousOn
          (fun t : ℝ => min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω)) (Icc 0 T) := by
        have hcont :
            Continuous (fun t : ℝ =>
              (t ⊔ tGrid T n) ⊓ tauHit (bmCoord B) T n ω) :=
          Continuous.inf
            (Continuous.sup (continuous_id : Continuous fun t : ℝ => t)
              (continuous_const : Continuous fun _ : ℝ => tGrid T n))
            (continuous_const : Continuous fun _ : ℝ => tauHit (bmCoord B) T n ω)
        have heq :
            (fun t : ℝ => min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω)) =
              fun t : ℝ => (t ⊔ tGrid T n) ⊓ tauHit (bmCoord B) T n ω :=
          funext fun t => rfl
        exact (heq ▸ hcont).continuousOn
      have hnonneg : ∀ t ∈ Icc 0 T,
          0 ≤ min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω) := fun t ht =>
        le_min (ht.1.trans (le_max_left _ _))
          ((tGrid_mem hT n).1.trans (tauHit_mem_Icc hT (bmCoord B) n ω).1)
      have hcomp : ContinuousOn
          (fun t : ℝ =>
            bmCoord B (min (max t (tGrid T n)) (tauHit (bmCoord B) T n ω)) ω)
          (Icc 0 T) :=
        hB.comp harg fun t ht => mem_Ici.mpr (hnonneg t ht)
      have hconstC : ContinuousOn (fun _ : ℝ => doublingC (bmCoord B) T n ω) (Icc 0 T) :=
        continuousOn_const
      have hconstB : ContinuousOn (fun _ : ℝ => bmCoord B (tGrid T n) ω) (Icc 0 T) :=
        continuousOn_const
      refine (hconstC.mul (hcomp.sub hconstB)).congr fun t _ => ?_
      simp [piece, hE]
    · have h0 : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 T) := continuousOn_const
      refine h0.congr fun t _ => ?_
      simp [piece, hE]
  have hsumC : ∀ M : ℕ, ContinuousOn (fun t => ∑ n ∈ Finset.range M, piece n t) (Icc 0 T) := by
    intro M
    induction M with
    | zero => simp; exact continuousOn_const
    | succ M ih =>
      have hrew :
          (fun t => ∑ n ∈ Finset.range (M + 1), piece n t) =
            fun t => (∑ n ∈ Finset.range M, piece n t) + piece M t :=
        funext fun t => Finset.sum_range_succ (fun n => piece n t) M
      rw [hrew]
      exact ContinuousOn.add ih (hpieces M)
  exact (hsumC N).congr fun t _ => hsum t


/-- Uniform left-endpoint of the `n`-partition of `[0, t]`. -/
def riemannTime (t : ℝ) (n k : ℕ) : ℝ := (k : ℝ) * t / (n + 1 : ℝ)

lemma riemannTime_zero (t : ℝ) (n : ℕ) : riemannTime t n 0 = 0 := by
  simp [riemannTime]

lemma riemannTime_last (t : ℝ) (n : ℕ) : riemannTime t n (n + 1) = t := by
  simp only [riemannTime, Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel_left₀ t (by positivity)

lemma riemannTime_mono {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    riemannTime t n k ≤ riemannTime t n l := by
  simp only [riemannTime]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) ht)
    (by positivity)

lemma riemannTime_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) : 0 ≤ riemannTime t n k := by
  simp only [riemannTime]
  exact div_nonneg (mul_nonneg k.cast_nonneg ht) (by positivity)

lemma riemannTime_le_t {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    riemannTime t n k ≤ t := by
  simpa [riemannTime_last] using riemannTime_mono ht n hk

lemma riemannTime_mesh (t : ℝ) (n k : ℕ) :
    riemannTime t n (k + 1) - riemannTime t n k = t / (n + 1 : ℝ) := by
  simp only [riemannTime, Nat.cast_succ]
  field_simp
  ring

lemma riemannTime_sub_eq {t : ℝ} (n : ℕ) (k l : ℕ) :
    riemannTime t n l - riemannTime t n k =
      ((l : ℝ) - (k : ℝ)) * t / (n + 1 : ℝ) := by
  simp only [riemannTime]
  field_simp

lemma itoRiemannSum_eq_riemannTime (K B : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemannSum K B t n ω =
      ∑ k : Fin (n + 1),
        K (riemannTime t n k.val) ω *
          (B (riemannTime t n (k.val + 1)) ω - B (riemannTime t n k.val) ω) := by
  simp [itoRiemannSum, riemannTime]

/-- Left-point Riemann sums of the indicator of `(a, b]` against a path `B`. -/
def itoRiemannSumIndicator (B : ℝ → Ω → ℝ) (t a b : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin (n + 1),
    if a < riemannTime t n k.val ∧ riemannTime t n k.val ≤ b then
      B (riemannTime t n (k.val + 1)) ω - B (riemannTime t n k.val) ω
    else 0

lemma itoRiemannSum_indicator_eq (B : ℝ → Ω → ℝ) (t a b : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemannSum (fun s _ => if a < s ∧ s ≤ b then (1 : ℝ) else 0) B t n ω =
      itoRiemannSumIndicator B t a b n ω := by
  simp [itoRiemannSum_eq_riemannTime, itoRiemannSumIndicator, ite_mul, one_mul, zero_mul]


lemma sum_Icc_successive_sub (g : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Icc m n, (g (k + 1) - g k) = g (n + 1) - g m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hmn), ih]
    ring

/-- The left endpoints of the partition that fall in `(a, b]`. -/
def riemannRect (t a b : ℝ) (n k : ℕ) : Prop :=
  a < riemannTime t n k ∧ riemannTime t n k ≤ b

lemma itoRiemannSumIndicator_eq_sum_range (B : ℝ → Ω → ℝ) (t a b : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemannSumIndicator B t a b n ω =
      ∑ k ∈ Finset.range (n + 1),
        if a < riemannTime t n k ∧ riemannTime t n k ≤ b then
          B (riemannTime t n (k + 1)) ω - B (riemannTime t n k) ω
        else 0 := by
  -- `∑ k : Fin (n+1), f k.val = ∑ k ∈ range (n+1), f k`
  have hsum : ∀ f : ℕ → ℝ,
      ∑ k : Fin (n + 1), f k.val = ∑ k ∈ Finset.range (n + 1), f k := fun f => by
    refine Finset.sum_bij (fun (k : Fin (n + 1)) _ => (k.val : ℕ)) ?_ ?_ ?_ ?_
    · intro k _
      exact Finset.mem_range.mpr k.isLt
    · intro k l _ _ hkl
      exact Fin.ext hkl
    · intro k hk
      exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro k _
      rfl
  simp only [itoRiemannSumIndicator]
  exact hsum fun k =>
    if a < riemannTime t n k ∧ riemannTime t n k ≤ b then
      B (riemannTime t n (k + 1)) ω - B (riemannTime t n k) ω
    else 0

lemma itoRiemannSumIndicator_empty (B : ℝ → Ω → ℝ) {t a b : ℝ} {n : ℕ} (ω : Ω)
    (h : ∀ k < n + 1, ¬ riemannRect t a b n k) :
    itoRiemannSumIndicator B t a b n ω = 0 := by
  rw [itoRiemannSumIndicator_eq_sum_range]
  exact Finset.sum_eq_zero fun k hk => by
    have hlt : k < n + 1 := Finset.mem_range.mp hk
    have hnr : ¬ (a < riemannTime t n k ∧ riemannTime t n k ≤ b) := by
      simpa [riemannRect] using h k hlt
    simp [hnr]

/-- Witness: the last left endpoint `n · t / (n+1)` lies in `(a, b]` when the mesh is small
and `b` reaches up to `t`. -/
lemma riemannRect_last {t a b : ℝ} {n : ℕ} (_ht : 0 ≤ t)
    (hmesh : t / (n + 1 : ℝ) < t - a) (hbn : t - t / (n + 1 : ℝ) ≤ b) :
    riemannRect t a b n n := by
  have htlt : riemannTime t n n = t - t / (n + 1 : ℝ) := by
    have := riemannTime_mesh t n n
    rw [riemannTime_last] at this
    linarith
  refine ⟨?_, ?_⟩
  · rw [htlt]
    linarith
  · rw [htlt]
    exact hbn


lemma itoRiemannSumIndicator_Icc (B : ℝ → Ω → ℝ) {t a b : ℝ} {n kmin kmax : ℕ} (ω : Ω)
    (hmax : kmax ≤ n) (hle : kmin ≤ kmax)
    (hiff : ∀ k < n + 1, riemannRect t a b n k ↔ kmin ≤ k ∧ k ≤ kmax) :
    itoRiemannSumIndicator B t a b n ω =
      B (riemannTime t n (kmax + 1)) ω - B (riemannTime t n kmin) ω := by
  rw [itoRiemannSumIndicator_eq_sum_range]
  have hfilter :
      (∑ k ∈ Finset.range (n + 1),
          if a < riemannTime t n k ∧ riemannTime t n k ≤ b then
            B (riemannTime t n (k + 1)) ω - B (riemannTime t n k) ω
          else 0) =
        ∑ k ∈ Finset.Icc kmin kmax,
          (B (riemannTime t n (k + 1)) ω - B (riemannTime t n k) ω) := by
    trans ∑ k ∈ (Finset.range (n + 1)).filter
        (fun k => a < riemannTime t n k ∧ riemannTime t n k ≤ b),
        (B (riemannTime t n (k + 1)) ω - B (riemannTime t n k) ω)
    · simp [Finset.sum_ite]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · intro ⟨hkn, hrec⟩
        exact (hiff k hkn).mp (by simpa [riemannRect] using hrec)
      · intro ⟨hk1, hk2⟩
        have hkn : k < n + 1 := lt_of_le_of_lt hk2 (Nat.lt_succ_of_le hmax)
        have hrec := (hiff k hkn).mpr ⟨hk1, hk2⟩
        exact ⟨hkn, by simpa [riemannRect] using hrec⟩
  rw [hfilter, sum_Icc_successive_sub (fun k => B (riemannTime t n k) ω) hle]

/-- If some left endpoint falls in `(a, b]`, the contributing indices are a contiguous block. -/
lemma riemannRect_block {t a b : ℝ} (ht : 0 ≤ t) {n : ℕ}
    (hex : ∃ k, k ≤ n ∧ riemannRect t a b n k) :
    let kmin := Nat.find hex
    let kmax := Nat.findGreatest (fun k => riemannRect t a b n k) n
    kmin ≤ kmax ∧ kmax ≤ n ∧
      ∀ k < n + 1, riemannRect t a b n k ↔ kmin ≤ k ∧ k ≤ kmax := by
  intro kmin kmax
  have hmin := Nat.find_spec hex
  have hmax_le : kmax ≤ n := Nat.findGreatest_le n
  have hmax_P : riemannRect t a b n kmax :=
    Nat.findGreatest_spec (P := fun k => riemannRect t a b n k) hmin.1 hmin.2
  have hle : kmin ≤ kmax :=
    Nat.le_findGreatest hmin.1 hmin.2
  refine ⟨hle, hmax_le, fun k hkn => ⟨fun hrec => ?fwd, fun hmem => ?bwd⟩⟩
  · have hk_le : k ≤ n := Nat.lt_succ_iff.mp hkn
    exact ⟨Nat.find_min' hex ⟨hk_le, hrec⟩,
      Nat.le_findGreatest hk_le hrec⟩
  · have hmono₁ : riemannTime t n kmin ≤ riemannTime t n k :=
      riemannTime_mono ht n hmem.1
    have hmono₂ : riemannTime t n k ≤ riemannTime t n kmax :=
      riemannTime_mono ht n hmem.2
    have hminR : riemannRect t a b n kmin := hmin.2
    have hmaxR : riemannRect t a b n kmax := hmax_P
    refine ⟨lt_of_lt_of_le hminR.1 hmono₁, hmono₂.trans hmaxR.2⟩

lemma itoRiemannSum_const_indicator (B : ℝ → Ω → ℝ) (c t a b : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemannSum (fun s _ => if a < s ∧ s ≤ b then c else 0) B t n ω =
      c * itoRiemannSumIndicator B t a b n ω := by
  simp only [itoRiemannSum_eq_riemannTime, itoRiemannSumIndicator, ite_mul, zero_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_ite, mul_zero, mul_sub]

lemma itoRiemannSum_add (K₁ K₂ B : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemannSum (fun s ω => K₁ s ω + K₂ s ω) B t n ω =
      itoRiemannSum K₁ B t n ω + itoRiemannSum K₂ B t n ω := by
  simp [itoRiemannSum, add_mul, Finset.sum_add_distrib]

lemma itoRiemannSum_fun_sum (Ks : ℕ → ℝ → Ω → ℝ) (B : ℝ → Ω → ℝ)
    (t : ℝ) (N n : ℕ) (ω : Ω) :
    itoRiemannSum (fun s ω => ∑ m ∈ Finset.range N, Ks m s ω) B t n ω =
      ∑ m ∈ Finset.range N, itoRiemannSum (Ks m) B t n ω := by
  induction N with
  | zero => simp [itoRiemannSum]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [itoRiemannSum_add, ih]

/-- After the first hit, `doublingK` is a finite sum of stopped blocks. -/
lemma doublingK_eq_sum {T : ℝ} {N : ℕ} {ω : Ω} (B : ℝ → Ω → ℝ)
    (hN : ω ∉ nonHitPrefix B T N) (s : ℝ) :
    doublingK B T s ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
          then doublingC B T n ω else 0) := by
  have hvan : ∀ n ≥ N, ω ∉ nonHitPrefix B T n := by
    intro n hn
    induction hn with
    | refl => exact hN
    | step _ ih => exact fun h => ih h.1
  exact tsum_eq_sum fun n hn => by
    have hge : N ≤ n := by
      simp only [Finset.mem_range, not_lt] at hn
      exact hn
    simp [hvan n hge]



lemma riemannTime_mesh_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => t / (n + 1 : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

lemma riemannTime_n_eq (t : ℝ) (n : ℕ) :
    riemannTime t n n = t - t / (n + 1 : ℝ) := by
  have hm := riemannTime_mesh t n n
  rw [riemannTime_last] at hm
  linarith

/-- If `0 ≤ a < min t b`, some left endpoint eventually falls in `(a, b]`. -/
lemma riemannRect_eventually {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (h : a < min t b) :
    ∀ᶠ n : ℕ in atTop, ∃ k, k ≤ n ∧ riemannRect t a b n k := by
  have htpos : 0 < t :=
    lt_of_le_of_lt ha (lt_of_lt_of_le h (min_le_left _ _))
  have hpos : 0 < min t b - a := sub_pos.mpr h
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (riemannTime_mesh_tendsto t) ((min t b - a) / 2) (half_pos hpos)
  refine eventually_atTop.mpr ⟨N, fun n hnN => ?_⟩
  have hδ : t / (n + 1 : ℝ) < (min t b - a) / 2 := by
    have := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg ht (by positivity))] at this
    exact this
  have hmesh : t / (n + 1 : ℝ) < min t b - a := hδ.trans (half_lt_self hpos)
  set δ : ℝ := t / (n + 1 : ℝ)
  have hδpos : 0 < δ := div_pos htpos (by positivity)
  by_cases hlast : riemannTime t n n ≤ min t b
  · refine ⟨n, le_rfl, ⟨?_, hlast.trans (min_le_right _ _)⟩⟩
    rw [riemannTime_n_eq]
    linarith [hmesh.trans_le (sub_le_sub_right (min_le_left t b) a)]
  · have hlt : min t b < riemannTime t n n := lt_of_not_ge hlast
    have hle_t : riemannTime t n n ≤ t := riemannTime_le_t ht n (Nat.le_succ n)
    have hmin_ne : min t b ≠ t := ne_of_lt (hlt.trans_le hle_t)
    have hminb : min t b = b := by
      rcases le_total t b with htb | hbt
      · rw [min_eq_left htb] at hmin_ne ⊢
        exact (hmin_ne rfl).elim
      · exact min_eq_right hbt
    let k := Nat.floor (b / δ)
    have hb_nonneg : 0 ≤ b :=
      le_trans ha (le_of_lt (lt_of_lt_of_le h (min_le_right _ _)))
    have hk_le_n : k ≤ n := by
      have hcast : (k : ℝ) < (n + 1 : ℝ) := by
        have hk1 : (k : ℝ) ≤ b / δ := Nat.floor_le (div_nonneg hb_nonneg hδpos.le)
        have hbt : b < t := by
          rw [← hminb]
          exact lt_of_le_of_ne (min_le_left _ _) hmin_ne
        have htδ : t = (n + 1 : ℝ) * δ := by
          simp only [δ]
          field_simp
        have : b / δ < (n + 1 : ℝ) := by
          rw [div_lt_iff₀ hδpos, ← htδ]
          exact hbt
        exact hk1.trans_lt this
      have hcast' : (k : ℝ) < (n.succ : ℝ) := by
        simpa [Nat.cast_succ] using hcast
      exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hcast')
    have hk_mul_le : (k : ℝ) * δ ≤ b :=
      (le_div_iff₀ hδpos).mp (Nat.floor_le (div_nonneg hb_nonneg hδpos.le))
    have hk_mul_gt : a < (k : ℝ) * δ := by
      have hfloor : b / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one (b / δ)
      have : b < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδpos).mp hfloor
      have : b - δ < (k : ℝ) * δ := by linarith
      have : a < b - δ := by
        rw [← hminb] at hmesh
        linarith
      exact this.trans ‹b - δ < (k : ℝ) * δ›
    refine ⟨k, hk_le_n, ?_⟩
    have hρ : riemannTime t n k = (k : ℝ) * δ := by
      simp only [riemannTime, δ]
      ring
    unfold riemannRect
    rw [hρ]
    exact ⟨hk_mul_gt, hk_mul_le⟩


lemma find_riemann_pos {t a b : ℝ} (ha : 0 ≤ a) {n : ℕ}
    (hex : ∃ k, k ≤ n ∧ riemannRect t a b n k) :
    0 < Nat.find hex := by
  have hspec := Nat.find_spec hex
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have htime : riemannTime t n (Nat.find hex) = 0 := by rw [h0, riemannTime_zero]
  have : a < 0 := by
    have := hspec.2.1
    rwa [htime] at this
  exact this.not_ge ha

lemma riemannTime_find_le_add_mesh {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) {n : ℕ}
    (hex : ∃ k, k ≤ n ∧ riemannRect t a b n k) :
    riemannTime t n (Nat.find hex) ≤ a + t / (n + 1 : ℝ) := by
  set kmin := Nat.find hex
  have hspec := Nat.find_spec hex
  have hkpos : 0 < kmin := find_riemann_pos ha hex
  have hblk := riemannRect_block ht hex
  have hkn : kmin - 1 < n + 1 :=
    (Nat.sub_le kmin 1).trans_lt (Nat.lt_succ_of_le hspec.1)
  have hprev : ¬ riemannRect t a b n (kmin - 1) := by
    intro hrec
    have hle : kmin ≤ kmin - 1 := ((hblk.2.2 (kmin - 1) hkn).mp hrec).1
    exact (Nat.not_le_of_gt (Nat.sub_lt hkpos Nat.one_pos)) hle
  have hsucc :
      riemannTime t n kmin = riemannTime t n (kmin - 1) + t / (n + 1 : ℝ) := by
    have hm := riemannTime_mesh t n (kmin - 1)
    have : kmin - 1 + 1 = kmin := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
    rw [this] at hm
    linarith
  have hprev_le : riemannTime t n (kmin - 1) ≤ a := by
    have hnr : ¬ (a < riemannTime t n (kmin - 1) ∧ riemannTime t n (kmin - 1) ≤ b) := by
      simpa [riemannRect] using hprev
    by_contra hgt
    have hlt' : a < riemannTime t n (kmin - 1) := lt_of_not_ge hgt
    have hmax_P : riemannRect t a b n (Nat.findGreatest (fun k => riemannRect t a b n k) n) :=
      Nat.findGreatest_spec (P := fun k => riemannRect t a b n k) hspec.1 hspec.2
    have hle_b : riemannTime t n (kmin - 1) ≤ b := by
      have hle1 : riemannTime t n (kmin - 1) ≤ riemannTime t n kmin :=
        riemannTime_mono ht n (Nat.sub_le _ _)
      have hle2 : riemannTime t n kmin ≤
          riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n) :=
        riemannTime_mono ht n hblk.1
      exact hle1.trans (hle2.trans hmax_P.2)
    exact hnr ⟨hlt', hle_b⟩
  linarith

lemma riemannTime_findGreatest_succ_bounds {t a b : ℝ} (ht : 0 ≤ t) {n : ℕ}
    (hex : ∃ k, k ≤ n ∧ riemannRect t a b n k) :
    min t b ≤
        riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1) ∧
      riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1) ≤
        min t b + t / (n + 1 : ℝ) := by
  set kmax := Nat.findGreatest (fun k => riemannRect t a b n k) n
  have hmax_le : kmax ≤ n := Nat.findGreatest_le n
  have hmin := Nat.find_spec hex
  have hmax_P : riemannRect t a b n kmax :=
    Nat.findGreatest_spec (P := fun k => riemannRect t a b n k) hmin.1 hmin.2
  have hmesh_eq := riemannTime_mesh t n kmax
  have hle_t : riemannTime t n (kmax + 1) ≤ t :=
    riemannTime_le_t ht n (Nat.succ_le_succ hmax_le)
  have hle_bmesh : riemannTime t n (kmax + 1) ≤ b + t / (n + 1 : ℝ) := by
    have : riemannTime t n kmax ≤ b := hmax_P.2
    linarith
  by_cases hkn : kmax = n
  · constructor
    · simp [hkn, riemannTime_last]
    · -- `t - mesh ≤ b` when `kmax = n`, since `nδ ≤ b`.
      have hb : riemannTime t n n ≤ b := by
        convert hmax_P.2
        exact hkn.symm
      have : riemannTime t n (n + 1) ≤ min t b + t / (n + 1 : ℝ) := by
        rw [riemannTime_last]
        have htm : t = riemannTime t n n + t / (n + 1 : ℝ) := by
          rw [riemannTime_n_eq]; ring
        have h1 : t ≤ b + t / (n + 1 : ℝ) := by linarith
        have h2 : t ≤ t + t / (n + 1 : ℝ) :=
          le_add_of_nonneg_right (div_nonneg ht (by positivity))
        simpa [min_add_add_right] using le_min h2 h1
      simpa [hkn] using this
  · have hlt : kmax < n := lt_of_le_of_ne hmax_le hkn
    have hnext : kmax + 1 ≤ n := Nat.succ_le_of_lt hlt
    have hnot : ¬ riemannRect t a b n (kmax + 1) := fun hrec =>
      Nat.not_le_of_gt (Nat.lt_succ_self kmax) (Nat.le_findGreatest hnext hrec)
    have hgt_a : a < riemannTime t n (kmax + 1) :=
      lt_of_lt_of_le hmax_P.1 (riemannTime_mono ht n (Nat.le_succ kmax))
    have hgt_b : b < riemannTime t n (kmax + 1) := by
      have hnr : ¬ (a < riemannTime t n (kmax + 1) ∧ riemannTime t n (kmax + 1) ≤ b) := by
        simpa [riemannRect] using hnot
      exact lt_of_not_ge fun hle => hnr ⟨hgt_a, hle⟩
    have hb_lt_t : b < t := hgt_b.trans_le hle_t
    have hminb : min t b = b := min_eq_right hb_lt_t.le
    constructor
    · rw [hminb]; exact hgt_b.le
    · rw [hminb]; exact hle_bmesh

lemma itoRiemannSumIndicator_eq_zero_of_not_win (B : ℝ → Ω → ℝ) {t a b : ℝ}
    (ht : 0 ≤ t) (h : ¬ a < min t b) (n : ℕ) (ω : Ω) :
    itoRiemannSumIndicator B t a b n ω = 0 := by
  refine itoRiemannSumIndicator_empty B ω fun k hk hrec => ?_
  have hkt : riemannTime t n k ≤ t := riemannTime_le_t ht n (le_of_lt hk)
  have : a < min t b :=
    lt_min (hrec.1.trans_le hkt) (hrec.1.trans_le hrec.2)
  exact h this

lemma min_eq_of_not_win {t a b : ℝ} (hab : a ≤ b) (h : ¬ a < min t b) :
    min t a = min t b := by
  have hba : min t b ≤ a := le_of_not_gt h
  exact le_antisymm (min_le_min_left t hab)
    (le_min (min_le_left _ _) hba)

lemma itoRiemannSumIndicator_block (B : ℝ → Ω → ℝ) {t a b : ℝ} (ht : 0 ≤ t)
    {n : ℕ} (ω : Ω) (hex : ∃ k, k ≤ n ∧ riemannRect t a b n k) :
    itoRiemannSumIndicator B t a b n ω =
      B (riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1)) ω -
        B (riemannTime t n (Nat.find hex)) ω := by
  have hblk := riemannRect_block ht hex
  exact itoRiemannSumIndicator_Icc B ω hblk.2.1 hblk.1 hblk.2.2


/-- Left-point Riemann sums of `1_{(a,b]}` against a continuous path converge
to the increment `B_{min(t,b)} - B_{min(t,a)}`. -/
lemma tendsto_itoRiemannSum_indicator (B : ℝ → Ω → ℝ) {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω)
    (hB : ContinuousOn (fun u => B u ω) (Icc 0 t)) :
    Tendsto (fun n => itoRiemannSumIndicator B t a b n ω) atTop
      (𝓝 (B (min t b) ω - B (min t a) ω)) := by
  by_cases hwin : a < min t b
  · have huc : UniformContinuousOn (fun u => B u ω) (Icc 0 t) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hB
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨δ, hδpos, hδuc⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (riemannRect_eventually ht ha hwin)
    obtain ⟨N₂, hN₂⟩ :=
      Metric.tendsto_atTop.mp (riemannTime_mesh_tendsto t) δ hδpos
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hex : ∃ k, k ≤ n ∧ riemannRect t a b n k :=
      hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    have hmesh : t / (n + 1 : ℝ) < δ := by
      have := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg ht (by positivity))] at this
      exact this
    have ha_eq : min t a = a :=
      min_eq_right (le_of_lt (lt_of_lt_of_le hwin (min_le_left _ _)))
    have hleft : |riemannTime t n (Nat.find hex) - a| < δ := by
      have hgt : a < riemannTime t n (Nat.find hex) := (Nat.find_spec hex).2.1
      have hle := riemannTime_find_le_add_mesh ht ha hex
      rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      linarith
    have hright := riemannTime_findGreatest_succ_bounds ht hex
    have hright_abs :
        |riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1) -
          min t b| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hright.1)]
      linarith [hright.2]
    have hsum := itoRiemannSumIndicator_block B ht ω hex
    have hu :
        riemannTime t n (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1) ∈ Icc 0 t :=
      ⟨riemannTime_nonneg ht n _,
        riemannTime_le_t ht n (Nat.succ_le_succ (Nat.findGreatest_le n))⟩
    have hv : riemannTime t n (Nat.find hex) ∈ Icc 0 t :=
      ⟨riemannTime_nonneg ht n _,
        riemannTime_le_t ht n (le_trans (Nat.find_spec hex).1 (Nat.le_succ n))⟩
    have hp : min t b ∈ Icc 0 t :=
      ⟨le_min ht (le_trans ha hab), min_le_left _ _⟩
    have hq : min t a ∈ Icc 0 t :=
      ⟨le_min ht ha, min_le_left _ _⟩
    have hBu :
        dist (B (riemannTime t n
            (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1)) ω)
          (B (min t b) ω) < ε / 2 :=
      hδuc _ hu _ hp (by simpa [Real.dist_eq] using hright_abs)
    have hBv :
        dist (B (riemannTime t n (Nat.find hex)) ω) (B (min t a) ω) < ε / 2 :=
      hδuc _ hv _ hq (by simpa [Real.dist_eq, ha_eq] using hleft)
    have htri :
        dist (itoRiemannSumIndicator B t a b n ω) (B (min t b) ω - B (min t a) ω) < ε := by
      rw [hsum, Real.dist_eq]
      have hident :
          |(B (riemannTime t n
                (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1)) ω -
              B (riemannTime t n (Nat.find hex)) ω) -
            (B (min t b) ω - B (min t a) ω)| =
            |(B (riemannTime t n
                (Nat.findGreatest (fun k => riemannRect t a b n k) n + 1)) ω -
              B (min t b) ω) -
            (B (riemannTime t n (Nat.find hex)) ω - B (min t a) ω)| := by
        ring_nf
      rw [Real.dist_eq] at hBu hBv
      rw [hident]
      refine (abs_sub _ _).trans_lt ?_
      linarith
    exact htri
  · have hz : B (min t b) ω - B (min t a) ω = 0 := by
      rw [min_eq_of_not_win hab hwin, sub_self]
    have hconst : (fun n => itoRiemannSumIndicator B t a b n ω) = fun _ => 0 :=
      funext fun n => itoRiemannSumIndicator_eq_zero_of_not_win B ht hwin n ω
    rw [hz, hconst]
    exact tendsto_const_nhds


/-- Scalar multiple of an indicator block: the Riemann sums converge to
`c · (B_{min(t,b)} - B_{min(t,a)})`. -/
lemma tendsto_itoRiemannSum_const_indicator (B : ℝ → Ω → ℝ) (c : ℝ) {t a b : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω)
    (hB : ContinuousOn (fun u => B u ω) (Icc 0 t)) :
    Tendsto (fun n =>
        itoRiemannSum (fun s _ => if a < s ∧ s ≤ b then c else 0) B t n ω) atTop
      (𝓝 (c * (B (min t b) ω - B (min t a) ω))) := by
  simpa [itoRiemannSum_const_indicator] using
    (tendsto_itoRiemannSum_indicator B ht ha hab ω hB).const_mul c

/-- After the first hit, the Riemann sum of `doublingK` at a fixed path is the
corresponding finite sum of scaled indicator sums. -/
lemma itoRiemannSum_doublingK_eq {T : ℝ} {N : ℕ} {ω : Ω} (B : ℝ → Ω → ℝ)
    (hN : ω ∉ nonHitPrefix B T N) (t : ℝ) (m : ℕ) :
    itoRiemannSum (doublingK B T) B t m ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix B T n then
          doublingC B T n ω *
            itoRiemannSumIndicator B t (tGrid T n) (tauHit B T n ω) m ω
         else 0) := by
  have hK :
      itoRiemannSum (doublingK B T) B t m ω =
        itoRiemannSum (fun s _ => ∑ n ∈ Finset.range N,
          (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0)) B t m ω := by
    simp only [itoRiemannSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact doublingK_eq_sum (B := B) hN _
  rw [hK, itoRiemannSum_fun_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hE : ω ∈ nonHitPrefix B T n
  · have hpiece :
        (fun s (_ : Ω) =>
          if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0) =
        (fun s (_ : Ω) =>
          if tGrid T n < s ∧ s ≤ tauHit B T n ω then doublingC B T n ω else 0) := by
      funext s ω'
      simp [hE]
    rw [hpiece, itoRiemannSum_const_indicator]
    simp [hE]
  · have h0 :
        (fun s (_ : Ω) =>
          if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0) =
        fun _ _ => (0 : ℝ) := by
      funext s ω'
      simp [hE]
    rw [h0]
    simp [hE, itoRiemannSum]

/-- The wealth piece equals the truncated increment `c_n (B_{min(t,τ_n)} - B_{min(t,t_n)})`. -/
lemma doublingWealth_piece_eq_increment {T t : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < t
      then doublingC B T n ω * (B (min t (tauHit B T n ω)) ω - B (tGrid T n) ω)
      else 0) =
    (if ω ∈ nonHitPrefix B T n then
      doublingC B T n ω * (B (min t (tauHit B T n ω)) ω - B (min t (tGrid T n)) ω)
     else 0) := by
  by_cases hE : ω ∈ nonHitPrefix B T n
  · by_cases hlt : tGrid T n < t
    · have hmin : min t (tGrid T n) = tGrid T n := min_eq_right hlt.le
      simp [hE, hlt, hmin]
    · have hmin_a : min t (tGrid T n) = t := min_eq_left (not_lt.mp hlt)
      have hτ : tGrid T n ≤ tauHit B T n ω := (tauHit_mem_Icc hT B n ω).1
      have hmin_b : min t (tauHit B T n ω) = t :=
        min_eq_left (le_trans (not_lt.mp hlt) hτ)
      simp [hE, hlt, hmin_a, hmin_b, sub_self]
  · simp [hE]

/-- After the first hit, left-point Riemann sums of `doublingK` converge pathwise
to `doublingWealth` along a continuous driver. -/
lemma tendsto_itoRiemannSum_doublingK {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ)
    {N : ℕ} {ω : Ω} (hN : ω ∉ nonHitPrefix B T N) {t : ℝ} (ht0 : 0 ≤ t)
    (hB : ContinuousOn (fun u => B u ω) (Icc 0 t)) :
    Tendsto (fun m => itoRiemannSum (doublingK B T) B t m ω) atTop
      (𝓝 (doublingWealth B T t ω)) := by
  have hW : doublingWealth B T t ω =
      ∑ n ∈ Finset.range N,
        (if ω ∈ nonHitPrefix B T n then
          doublingC B T n ω *
            (B (min t (tauHit B T n ω)) ω - B (min t (tGrid T n)) ω)
         else 0) := by
    rw [doublingWealth_eq_sum (B := B) hN t]
    refine Finset.sum_congr rfl fun n _ => doublingWealth_piece_eq_increment hT B n ω
  have hfun :
      (fun m => itoRiemannSum (doublingK B T) B t m ω) =
        fun m => ∑ n ∈ Finset.range N,
          (if ω ∈ nonHitPrefix B T n then
            doublingC B T n ω *
              itoRiemannSumIndicator B t (tGrid T n) (tauHit B T n ω) m ω
           else 0) :=
    funext fun m => itoRiemannSum_doublingK_eq (B := B) hN t m
  rw [hfun, hW]
  refine tendsto_finsetSum (Finset.range N) fun n _ => ?_
  by_cases hE : ω ∈ nonHitPrefix B T n
  · simp only [hE, ↓reduceIte]
    have ha : 0 ≤ tGrid T n := (tGrid_mem hT n).1
    have hab : tGrid T n ≤ tauHit B T n ω := (tauHit_mem_Icc hT B n ω).1
    exact (tendsto_itoRiemannSum_indicator B ht0 ha hab ω hB).const_mul
      (doublingC B T n ω)
  · simp only [hE, ↓reduceIte]
    exact tendsto_const_nhds


/-- Pathwise continuous extension of `bmCoord` to all of `ℝ`, constant on `(-∞, 0]`. -/
lemma continuous_bmCoord_max (B : MultiBrownian Ω P 1) (ω : Ω) :
    Continuous (fun t : ℝ => bmCoord B (max 0 t) ω) :=
  (bmCoord_cont B ω).comp_continuous (continuous_const.max continuous_id)
    fun t => le_max_left 0 t

/-- Joint measurability of `(t, ω) ↦ B_{max(0,t)}(ω)`. -/
lemma measurable_uncurry_bmCoord_max (B : MultiBrownian Ω P 1) :
    Measurable (Function.uncurry fun t ω => bmCoord B (max 0 t) ω) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => continuous_bmCoord_max B ω) (fun t => bmCoord_meas B (max 0 t))

/-- Evaluation of a non-negative measurable time along a continuous adapted path. -/
lemma measurable_bmCoord_comp (B : MultiBrownian Ω P 1) {τ : Ω → ℝ}
    (hτ : Measurable τ) (hnn : ∀ ω, 0 ≤ τ ω) :
    Measurable (fun ω => bmCoord B (τ ω) ω) := by
  have h : Measurable (fun ω => bmCoord B (max 0 (τ ω)) ω) :=
    (measurable_uncurry_bmCoord_max B).comp (hτ.prodMk measurable_id)
  have heq : (fun ω => bmCoord B (τ ω) ω) =
      (fun ω => bmCoord B (max 0 (τ ω)) ω) :=
    funext fun ω => by rw [max_eq_right (hnn ω)]
  rwa [heq]


/-- The hitting time `τ_n` is measurable with respect to the ambient σ-algebra. -/
lemma measurable_tauHit (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Measurable (tauHit (bmCoord B) T n) := by
  refine measurable_of_Iic fun t => ?_
  change MeasurableSet {ω | tauHit (bmCoord B) T n ω ≤ t}
  by_cases ht0 : t < 0
  · have hempty : {ω | tauHit (bmCoord B) T n ω ≤ t} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun ω hω => by
        have hnn : 0 ≤ tauHit (bmCoord B) T n ω :=
          (tGrid_mem hT n).1.trans (tauHit_mem_Icc hT (bmCoord B) n ω).1
        exact (not_lt.mpr hnn) (hω.trans_lt ht0)
    rw [hempty]
    exact MeasurableSet.empty
  · by_cases htT : T ≤ t
    · have huniv : {ω | tauHit (bmCoord B) T n ω ≤ t} = Set.univ :=
        Set.eq_univ_iff_forall.mpr fun ω =>
          (tauHit_mem_Icc hT (bmCoord B) n ω).2.trans
            ((tGrid_mem hT (n + 1)).2.trans htT)
      rw [huniv]
      exact MeasurableSet.univ
    · have ht : t ∈ Icc 0 T := ⟨not_lt.mp ht0, le_of_not_ge htT⟩
      exact (pathFiltration B).le_ambient t _
        ((isStoppingTime_tauHit B hT n).2 t ht)

/-- Recursive grid wealth is measurable. -/
lemma measurable_doublingX (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ n, Measurable (doublingX (bmCoord B) T n)
  | 0 => by
    simp only [doublingX]
    exact measurable_const
  | n + 1 => by
    have hX := measurable_doublingX B hT n
    have hC :
        Measurable fun ω =>
          (1 - doublingX (bmCoord B) T n ω) / Real.sqrt (dtGrid T n) :=
      (measurable_const.sub hX).div_const _
    have hE : MeasurableSet (nonHitPrefix (bmCoord B) T n) :=
      (pathFiltration B).le_ambient (tGrid T n) _
        ((nonHitPrefix_props B hT).1 n)
    have hBτ : Measurable (fun ω => bmCoord B (tauHit (bmCoord B) T n ω) ω) :=
      measurable_bmCoord_comp B (measurable_tauHit B hT n) fun ω =>
        (tGrid_mem hT n).1.trans (tauHit_mem_Icc hT (bmCoord B) n ω).1
    have hBt : Measurable (bmCoord B (tGrid T n)) := bmCoord_meas B (tGrid T n)
    simp only [doublingX]
    exact hX.add (Measurable.ite hE (hC.mul (hBτ.sub hBt)) measurable_const)

lemma measurable_doublingC (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Measurable (doublingC (bmCoord B) T n) :=
  (measurable_const.sub (measurable_doublingX B hT n)).div_const _

/-- Off `(0, T)` every doubling block is empty, so `K_s = 0`. -/
lemma doublingK_eq_zero_of_not_mem_Ioo {T s : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ)
    (hs : s ∉ Ioo 0 T) (ω : Ω) : doublingK B T s ω = 0 := by
  have hterm :
      (fun n : ℕ =>
        if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
          then doublingC B T n ω else 0) = fun _ => 0 := by
    funext n
    by_cases hpos : 0 < s
    · have hsT : ¬ s < T := fun hst => hs ⟨hpos, hst⟩
      have hleτ : ¬ s ≤ tauHit B T n ω := by
        have hτlt : tauHit B T n ω < T :=
          lt_of_le_of_lt (tauHit_mem_Icc hT B n ω).2 (tGrid_lt_T hT (n + 1))
        exact not_le.mpr (lt_of_lt_of_le hτlt (not_lt.mp hsT))
      simp [hleτ]
    · have hlt : ¬ tGrid T n < s :=
        not_lt.mpr ((not_lt.mp hpos).trans (tGrid_mem hT n).1)
      simp [hlt]
  unfold doublingK
  rw [hterm, tsum_zero]

/-- On `(0, T)` only the finitely many blocks with `t_n < s` can be live. -/
lemma doublingK_eq_sum_nGrid {T s : ℝ} (hT : 0 < T) (hs0 : 0 < s) (hsT : s < T)
    (B : ℝ → Ω → ℝ) (ω : Ω) :
    doublingK B T s ω =
      ∑ n ∈ Finset.range (nGrid T s + 1),
        (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
          then doublingC B T n ω else 0) := by
  have hbound : ∀ n, nGrid T s + 1 ≤ n → ¬ tGrid T n < s := by
    intro n hn
    have hmono : tGrid T (nGrid T s + 1) ≤ tGrid T n := tGrid_mono hT hn
    exact not_lt.mpr ((nGrid_spec hT hs0 hsT).2.trans hmono)
  exact tsum_eq_sum fun n hn => by
    have hge : nGrid T s + 1 ≤ n := le_of_not_gt (Finset.mem_range.not.mp hn)
    simp [hbound n hge]

/-- Each time-slice of the doubling integrand is measurable. -/
lemma measurable_doublingK (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (s : ℝ) :
    Measurable (doublingK (bmCoord B) T s) := by
  by_cases hs : s ∈ Ioo 0 T
  · have hs0 : 0 < s := hs.1
    have hsT : s < T := hs.2
    have hterm : ∀ n, Measurable fun ω =>
        if ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
            s ≤ tauHit (bmCoord B) T n ω
          then doublingC (bmCoord B) T n ω else 0 := by
      intro n
      have hE : MeasurableSet (nonHitPrefix (bmCoord B) T n) :=
        (pathFiltration B).le_ambient (tGrid T n) _
          ((nonHitPrefix_props B hT).1 n)
      have hτ : MeasurableSet {ω | s ≤ tauHit (bmCoord B) T n ω} :=
        (measurable_tauHit B hT n) measurableSet_Ici
      have hp : MeasurableSet
          {ω | ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
            s ≤ tauHit (bmCoord B) T n ω} := by
        by_cases hlt : tGrid T n < s
        · have heq :
              {ω | ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
                s ≤ tauHit (bmCoord B) T n ω} =
              nonHitPrefix (bmCoord B) T n ∩
                {ω | s ≤ tauHit (bmCoord B) T n ω} := by
            ext ω; simp [hlt]
          rw [heq]
          exact hE.inter hτ
        · have heq :
              {ω | ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
                s ≤ tauHit (bmCoord B) T n ω} = ∅ := by
            ext ω; simp [hlt]
          rw [heq]
          exact MeasurableSet.empty
      exact Measurable.ite hp (measurable_doublingC B hT n) measurable_const
    have heq : doublingK (bmCoord B) T s =
        fun ω => ∑ n ∈ Finset.range (nGrid T s + 1),
          (if ω ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < s ∧
              s ≤ tauHit (bmCoord B) T n ω
            then doublingC (bmCoord B) T n ω else 0) :=
      funext fun ω => doublingK_eq_sum_nGrid hT hs0 hsT (bmCoord B) ω
    rw [heq]
    exact Finset.measurable_fun_sum _ fun n _ => hterm n
  · have heq : doublingK (bmCoord B) T s = fun _ => 0 :=
      funext fun ω => doublingK_eq_zero_of_not_mem_Ioo hT (bmCoord B) hs ω
    rw [heq]
    exact measurable_const

lemma measurable_itoRiemannSum (K : ℝ → Ω → ℝ) (B : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ)
    (hK : ∀ k : Fin (n + 1), Measurable (K (k * t / (n + 1 : ℝ))))
    (hB : ∀ s, Measurable (B s)) :
    Measurable (itoRiemannSum K B t n) := by
  unfold itoRiemannSum
  exact Finset.measurable_fun_sum _ fun k _ =>
    (hK k).mul ((hB _).sub (hB _))

/-- The doubling wealth is the Itô integral of `doublingK` against `B` (no glue
parameters): `V_0 = 0`, paths are a.s. continuous, and the left-point Riemann
sums converge to `V_t` in probability on `[0, T]`. -/
lemma isItoIntegral_doublingWealth (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    IsItoIntegral P (bmCoord B) (doublingK (bmCoord B) T)
      (doublingWealth (bmCoord B) T) T := by
  refine ⟨fun ω => doublingWealth_zero hT (bmCoord B) ω, ?_, ?_⟩
  · exact doublingWealth_continuousOn_ae B hT
  · intro t ht
    have hmeas : ∀ n, Measurable
        (itoRiemannSum (doublingK (bmCoord B) T) (bmCoord B) t n) :=
      fun n => measurable_itoRiemannSum _ _ t n
        (fun _ => measurable_doublingK B hT _) (fun _ => bmCoord_meas B _)
    refine tendstoInMeasure_of_tendsto_ae
      (fun n => (hmeas n).aestronglyMeasurable) ?_
    have hhit : ∀ᵐ ω ∂P, ∃ N : ℕ, ω ∉ nonHitPrefix (bmCoord B) T N := by
      have h0 := (nonHitPrefix_props B hT).2.2
      refine (measure_eq_zero_iff_ae_notMem.mp h0).mono fun ω hω => ?_
      simpa [mem_iInter] using hω
    filter_upwards [hhit] with ω ⟨N, hN⟩
    exact tendsto_itoRiemannSum_doublingK hT (bmCoord B) hN ht.1
      (bmCoord_cont_Icc B ω ht.1)




/-- Scaling identity: `k < s * 2^m / T` iff `k * T / 2^m < s`. -/
lemma dyadic_lt_iff {T s : ℝ} (hT : 0 < T) (k m : ℕ) :
    (k : ℝ) < s * (2 ^ m : ℝ) / T ↔ (k : ℝ) * T / (2 ^ m : ℝ) < s := by
  have h2 : 0 < (2 ^ m : ℝ) := by positivity
  rw [lt_div_iff₀ hT, div_lt_iff₀ h2, mul_comm s]

lemma dyadic_le_iff {T s : ℝ} (hT : 0 < T) (k m : ℕ) :
    s * (2 ^ m : ℝ) / T ≤ (k : ℝ) ↔ s ≤ (k : ℝ) * T / (2 ^ m : ℝ) := by
  have h2 : 0 < (2 ^ m : ℝ) := by positivity
  rw [div_le_iff₀ hT, le_div_iff₀ h2, mul_comm s]

/-- The unique dyadic slot of level `m` containing `s ∈ (0, T]`. -/
lemma exists_dyadic_Ioc {T s : ℝ} (hT : 0 < T) (hs0 : 0 < s) (hsT : s ≤ T) (m : ℕ) :
    ∃ k : ℕ, k + 1 ≤ 2 ^ m ∧
      (k : ℝ) * T / (2 ^ m : ℝ) < s ∧
        s ≤ (k + 1 : ℝ) * T / (2 ^ m : ℝ) := by
  set x := s * (2 ^ m : ℝ) / T
  have hxpos : 0 < x := div_pos (mul_pos hs0 (by positivity)) hT
  have hxle : x ≤ (2 ^ m : ℝ) := by
    have h2 : 0 ≤ (2 ^ m : ℝ) := by positivity
    have : s * (2 ^ m : ℝ) ≤ T * (2 ^ m : ℝ) :=
      mul_le_mul_of_nonneg_right hsT h2
    rw [mul_comm T] at this
    exact (div_le_iff₀ hT).mpr this
  have hceil_pos : 1 ≤ ⌈x⌉₊ := Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hxpos)
  have hceil_le : ⌈x⌉₊ ≤ 2 ^ m := Nat.ceil_le.mpr (by exact_mod_cast hxle)
  refine ⟨⌈x⌉₊ - 1, ?_, ?_, ?_⟩
  · exact (Nat.sub_add_cancel hceil_pos).symm ▸ hceil_le
  · have hcast : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hceil_pos, Nat.cast_one]
    have hlt : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
      rw [hcast]
      have hnot : ¬ x ≤ (⌈x⌉₊ : ℝ) - 1 := by
        intro hle
        have : ⌈x⌉₊ ≤ ⌈x⌉₊ - 1 :=
          Nat.ceil_le.mpr (by rwa [← hcast] at hle)
        exact (Nat.not_le.mpr (Nat.sub_one_lt_of_le hceil_pos le_rfl)) this
      exact not_le.mp hnot
    exact (dyadic_lt_iff hT (⌈x⌉₊ - 1) m).mp hlt
  · have hcancel : ⌈x⌉₊ - 1 + 1 = ⌈x⌉₊ := Nat.sub_add_cancel hceil_pos
    have hxk : x ≤ ((⌈x⌉₊ - 1 + 1 : ℕ) : ℝ) := by
      rw [hcancel]
      exact Nat.le_ceil x
    have hgoal := (dyadic_le_iff hT (⌈x⌉₊ - 1 + 1) m).mp hxk
    simpa [Nat.cast_succ] using hgoal

/-- Generating rectangles are measurable in `predSigma`. -/
lemma measurableSet_predRect {σAlg : ℝ → MeasurableSpace Ω} {T a b : ℝ} {A : Set Ω}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hA : MeasurableSet[σAlg a] A) :
    MeasurableSet[predSigma σAlg T] (Ioc a b ×ˢ A) :=
  MeasurableSpace.measurableSet_generateFrom ⟨a, b, A, ha, hab, hbT, hA, rfl⟩

/-- Width of a dyadic slot of level `m`. -/
lemma dyadic_width (T : ℝ) (m k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ) - (k : ℝ) * T / (2 ^ m : ℝ) =
      T / (2 ^ m : ℝ) := by
  rw [Nat.cast_succ, add_mul, one_mul, add_div, add_sub_cancel_left]

/-- The left-open stochastic interval `(a, τ] ∩ (0, T]` is predictable when `τ` is a
`[0, T]`-valued stopping time and `0 ≤ a ≤ T`. -/
lemma measurableSet_stochInterval {σAlg : ℝ → MeasurableSpace Ω} {T a : ℝ}
    (hT : 0 < T) (ha0 : 0 ≤ a) (haT : a ≤ T) (τ : Ω → ℝ)
    (hτ : IsStoppingTimeOn σAlg T τ) :
    MeasurableSet[predSigma σAlg T]
      {p : ℝ × Ω | a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T} := by
  let tPoint (m k : ℕ) : ℝ := (k : ℝ) * T / (2 ^ m : ℝ)
  let box (m k : ℕ) : Set (ℝ × Ω) :=
    Ioc (tPoint m k) (tPoint m (k + 1)) ×ˢ {ω | tPoint m k < τ ω}
  have hbox : ∀ m k, k + 1 ≤ 2 ^ m → MeasurableSet[predSigma σAlg T] (box m k) := by
    intro m k hk
    have htk0 : 0 ≤ tPoint m k :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.le) (by positivity)
    have htk_le : tPoint m k ≤ tPoint m (k + 1) := by
      have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_succ]; linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT.le)
        (by positivity)
    have htkT : tPoint m (k + 1) ≤ T := by
      have hk' : ((k + 1 : ℕ) : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast hk
      have : ((k + 1 : ℕ) : ℝ) * T ≤ T * (2 ^ m : ℝ) := by
        rw [mul_comm T]
        exact mul_le_mul_of_nonneg_right hk' hT.le
      exact (div_le_iff₀ (by positivity : 0 < (2 ^ m : ℝ))).mpr this
    have htIcc : tPoint m k ∈ Icc 0 T := ⟨htk0, htk_le.trans htkT⟩
    refine measurableSet_predRect htk0 htk_le htkT ?_
    have : {ω | tPoint m k < τ ω} = {ω | τ ω ≤ tPoint m k}ᶜ := by
      ext ω; simp [not_le]
    rw [this]
    exact (hτ.2 (tPoint m k) htIcc).compl
  have hrect : MeasurableSet[predSigma σAlg T] (Ioc a T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predRect ha0 haT le_rfl MeasurableSet.univ
  let U (m : ℕ) : Set (ℝ × Ω) := ⋃ k ∈ Finset.range (2 ^ m), box m k
  have hU : ∀ m, MeasurableSet[predSigma σAlg T] (U m) := fun m =>
    Finset.measurableSet_biUnion _ fun k hk =>
      hbox m k (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hI : MeasurableSet[predSigma σAlg T] (⋂ m, U m) :=
    MeasurableSet.iInter hU
  have hRmeas : MeasurableSet[predSigma σAlg T]
      ((Ioc a T ×ˢ (Set.univ : Set Ω)) ∩ ⋂ m, U m) :=
    hrect.inter hI
  have hSR : {p : ℝ × Ω | a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T} =
      (Ioc a T ×ˢ (Set.univ : Set Ω)) ∩ ⋂ m, U m := by
    ext ⟨s, ω⟩
    constructor
    · intro h
      have hs0 : 0 < s := lt_of_le_of_lt ha0 h.1
      refine ⟨⟨⟨h.1, h.2.2⟩, trivial⟩, ?_⟩
      rw [mem_iInter]
      intro m
      obtain ⟨k, hk, hklt, hkle⟩ := exists_dyadic_Ioc hT hs0 h.2.2 m
      refine mem_biUnion (Finset.mem_range.mpr (Nat.lt_of_succ_le hk)) ?_
      have hkle' : s ≤ tPoint m (k + 1) := by
        dsimp only [tPoint]
        simpa [Nat.cast_succ] using hkle
      exact ⟨⟨hklt, hkle'⟩, lt_of_lt_of_le hklt h.2.1⟩
    · intro ⟨⟨⟨has, hsT⟩, _⟩, hcap⟩
      refine ⟨has, ?_, hsT⟩
      have hε : ∀ m : ℕ, s - T / (2 ^ m : ℝ) < τ ω := by
        intro m
        have hm : (s, ω) ∈ U m := (mem_iInter.mp hcap) m
        rw [mem_iUnion₂] at hm
        obtain ⟨k, hk, hkmem⟩ := hm
        have hklt : k + 1 ≤ 2 ^ m :=
          Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        have hmem : s ∈ Ioc (tPoint m k) (tPoint m (k + 1)) ∧ tPoint m k < τ ω :=
          hkmem
        have hwidth : s - T / (2 ^ m : ℝ) ≤ tPoint m k := by
          have hsle : s ≤ tPoint m (k + 1) := hmem.1.2
          have hdiff : tPoint m (k + 1) - tPoint m k = T / (2 ^ m : ℝ) := by
            dsimp only [tPoint]
            simpa using dyadic_width T m k
          linarith
        exact lt_of_le_of_lt hwidth hmem.2
      have hlim0 : Tendsto (fun m : ℕ => s - T / (2 ^ m : ℝ)) atTop (𝓝 (s - 0)) :=
        tendsto_const_nhds.sub
          ((tendsto_const_nhds (x := T)).div_atTop
            (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
      have hlim : Tendsto (fun m : ℕ => s - T / (2 ^ m : ℝ)) atTop (𝓝 s) := by
        simpa using hlim0
      exact le_of_tendsto hlim (Eventually.of_forall fun m => (hε m).le)
  exact hSR ▸ hRmeas


/-- Nonnegativity of a dyadic grid point on `[0, T]`. -/
lemma dyadic_point_nonneg {T : ℝ} (hT : 0 ≤ T) (m k : ℕ) :
    0 ≤ (k : ℝ) * T / (2 ^ m : ℝ) :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) (by positivity)

lemma dyadic_point_mono {T : ℝ} (hT : 0 ≤ T) (m k : ℕ) :
    (k : ℝ) * T / (2 ^ m : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ) := by
  have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_succ]; linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) (by positivity)

lemma dyadic_point_le_T {T : ℝ} (hT : 0 ≤ T) {m k : ℕ} (hk : k ≤ 2 ^ m) :
    (k : ℝ) * T / (2 ^ m : ℝ) ≤ T := by
  have hk' : (k : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast hk
  have : (k : ℝ) * T ≤ T * (2 ^ m : ℝ) := by
    rw [mul_comm T]
    exact mul_le_mul_of_nonneg_right hk' hT
  exact (div_le_iff₀ (by positivity : 0 < (2 ^ m : ℝ))).mpr this

lemma dyadic_point_mem_Icc {T : ℝ} (hT : 0 ≤ T) {m k : ℕ} (hk : k ≤ 2 ^ m) :
    (k : ℝ) * T / (2 ^ m : ℝ) ∈ Icc 0 T :=
  ⟨dyadic_point_nonneg hT m k, dyadic_point_le_T hT hk⟩

/-- A point of `(0, T]` lies in at most one dyadic slot of a given level. -/
lemma dyadic_Ioc_unique {T s : ℝ} (hT : 0 < T) {m k k' : ℕ}
    (hk : (k : ℝ) * T / (2 ^ m : ℝ) < s ∧
      s ≤ ((k + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ))
    (hk' : (k' : ℝ) * T / (2 ^ m : ℝ) < s ∧
      s ≤ ((k' + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ)) :
    k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · have hle : ((k + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ) ≤
        (k' : ℝ) * T / (2 ^ m : ℝ) := by
      have : k + 1 ≤ k' := Nat.succ_le_of_lt h
      have hcast : ((k + 1 : ℕ) : ℝ) ≤ (k' : ℝ) := by exact_mod_cast this
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcast hT.le) (by positivity)
    linarith
  · exact h
  · have hle : ((k' + 1 : ℕ) : ℝ) * T / (2 ^ m : ℝ) ≤
        (k : ℝ) * T / (2 ^ m : ℝ) := by
      have : k' + 1 ≤ k := Nat.succ_le_of_lt h
      have hcast : ((k' + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcast hT.le) (by positivity)
    linarith

/-- Constant functions are measurable for an arbitrary σ-algebra on `Ω`. -/
lemma measurable_const_σAlg {m : MeasurableSpace Ω} (c : ℝ) :
    @Measurable Ω ℝ m inferInstance (fun _ => c) :=
  fun s _hs => by
    by_cases hmem : c ∈ s
    · have : (fun _ : Ω => c) ⁻¹' s = Set.univ := by
        ext ω; simp [hmem]
      rw [this]
      exact @MeasurableSet.univ Ω m
    · have : (fun _ : Ω => c) ⁻¹' s = ∅ := by
        ext ω; simp [hmem]
      rw [this]
      exact @MeasurableSet.empty Ω m

/-- Pointwise `if p then f else g` is measurable for an arbitrary σ-algebra on `Ω`. -/
lemma measurable_ite_σAlg {m : MeasurableSpace Ω} {p : Ω → Prop} [DecidablePred p]
    {f g : Ω → ℝ} (hp : MeasurableSet[m] {ω | p ω})
    (hf : ∀ ⦃s : Set ℝ⦄, MeasurableSet s → MeasurableSet[m] (f ⁻¹' s))
    (hg : ∀ ⦃s : Set ℝ⦄, MeasurableSet s → MeasurableSet[m] (g ⁻¹' s)) :
    ∀ ⦃s : Set ℝ⦄, MeasurableSet s →
      MeasurableSet[m] ((fun ω => if p ω then f ω else g ω) ⁻¹' s) := by
  intro s hs
  have hpre :
      (fun ω => if p ω then f ω else g ω) ⁻¹' s =
        ({ω | p ω} ∩ f ⁻¹' s) ∪ ({ω | p ω}ᶜ ∩ g ⁻¹' s) := by
    ext ω
    by_cases hpω : p ω
    · simp [hpω]
    · simp [hpω]
  rw [hpre]
  exact (hp.inter (hf hs)).union (hp.compl.inter (hg hs))

/-- The path filtration packaged as a Mathlib `Filtration`. -/
def pathFiltrationM (B : MultiBrownian Ω P 1) :
    Filtration ℝ (inferInstance : MeasurableSpace Ω) where
  seq := (pathFiltration B).σAlg
  mono' := fun _ _ hst => (pathFiltration B).mono hst
  le' := (pathFiltration B).le_ambient

/-- `B_{max(0,t)}` is `F_t`-measurable for every real `t`. -/
lemma measurable_bmCoord_max_adapted (B : MultiBrownian Ω P 1) (t : ℝ) :
    Measurable[(pathFiltration B).σAlg t] (fun ω => bmCoord B (max 0 t) ω) := by
  by_cases ht : 0 ≤ t
  · have heq : (fun ω => bmCoord B (max 0 t) ω) = bmCoord B t :=
      funext fun ω => by rw [max_eq_right ht]
    rw [heq]
    exact measurable_W_pathFiltration (T := t) B ⟨t, ht, le_rfl⟩ ⟨0, Nat.succ_pos 0⟩
  · have heq : (fun ω => bmCoord B (max 0 t) ω) = fun _ => (0 : ℝ) :=
      funext fun ω => by rw [max_eq_left (le_of_not_ge ht), bmCoord_zero]
    rw [heq]
    exact measurable_const_σAlg (m := (pathFiltration B).σAlg t) 0

lemma stronglyAdapted_bmCoord_max (B : MultiBrownian Ω P 1) :
    StronglyAdapted (pathFiltrationM B) (fun t ω => bmCoord B (max 0 t) ω) :=
  fun t => (measurable_bmCoord_max_adapted B t).stronglyMeasurable

lemma isStronglyProgressive_bmCoord_max (B : MultiBrownian Ω P 1) :
    IsStronglyProgressive (pathFiltrationM B) (fun t ω => bmCoord B (max 0 t) ω) :=
  (stronglyAdapted_bmCoord_max B).isStronglyProgressive_of_continuous
    (fun ω => continuous_bmCoord_max B ω)

/-- A `[0, T]`-valued `IsStoppingTimeOn` is a Mathlib stopping time of `pathFiltrationM`. -/
lemma isStoppingTime_pathFiltrationM (B : MultiBrownian Ω P 1) {T : ℝ} {τ : Ω → ℝ}
    (hτ : IsStoppingTimeOn (pathFiltration B).σAlg T τ) :
    IsStoppingTime (pathFiltrationM B) (fun ω => (τ ω : WithTop ℝ)) := by
  intro i
  have hset : {ω | (τ ω : WithTop ℝ) ≤ (i : WithTop ℝ)} = {ω | τ ω ≤ i} := by
    ext ω; simp
  rw [hset]
  by_cases hi0 : i < 0
  · have hempty : {ω | τ ω ≤ i} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun ω hω =>
        (not_lt.mpr (hτ.1 ω).1) (hω.trans_lt hi0)
    rw [hempty]
    exact @MeasurableSet.empty Ω ((pathFiltration B).σAlg i)
  · by_cases hiT : T < i
    · have huniv : {ω | τ ω ≤ i} = Set.univ :=
        Set.eq_univ_iff_forall.mpr fun ω => (hτ.1 ω).2.trans hiT.le
      rw [huniv]
      exact @MeasurableSet.univ Ω ((pathFiltration B).σAlg i)
    · have hi : i ∈ Icc 0 T := ⟨not_lt.mp hi0, le_of_not_gt hiT⟩
      exact hτ.2 i hi

/-- Evaluation of `B` at a `[0, T]`-valued stopping time `τ ≤ t` is `F_t`-measurable. -/
lemma measurable_bmCoord_eval_le (B : MultiBrownian Ω P 1) {T t : ℝ}
    (_ht : t ∈ Icc 0 T) {τ : Ω → ℝ}
    (hτ : IsStoppingTimeOn (pathFiltration B).σAlg T τ)
    (hτ_le : ∀ ω, τ ω ≤ t) :
    Measurable[(pathFiltration B).σAlg t] (fun ω => bmCoord B (τ ω) ω) := by
  have hST := isStoppingTime_pathFiltrationM B hτ
  have hτ_le' : ∀ ω, (τ ω : WithTop ℝ) ≤ (t : WithTop ℝ) := fun ω =>
    WithTop.coe_le_coe.mpr (hτ_le ω)
  have hsm :
      StronglyMeasurable[(pathFiltrationM B) t]
        (stoppedValue (fun u ω => bmCoord B (max 0 u) ω)
          (fun ω => (τ ω : WithTop ℝ))) :=
    stronglyMeasurable_stoppedValue_of_le
      (isStronglyProgressive_bmCoord_max B) hST hτ_le'
  have heq :
      stoppedValue (fun u ω => bmCoord B (max 0 u) ω)
          (fun ω => (τ ω : WithTop ℝ)) =
        fun ω => bmCoord B (τ ω) ω := by
    funext ω
    have hnn : 0 ≤ τ ω := (hτ.1 ω).1
    simp [stoppedValue, WithTop.untopA, max_eq_right hnn]
  rw [← heq]
  exact hsm.measurable

/-- Arithmetic of measurable functions, with the σ-algebra passed explicitly. -/
lemma measurable_add_σAlg {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : @Measurable Ω ℝ m inferInstance f)
    (hg : @Measurable Ω ℝ m inferInstance g) :
    @Measurable Ω ℝ m inferInstance (fun ω => f ω + g ω) :=
  hf.add hg

lemma measurable_sub_σAlg {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : @Measurable Ω ℝ m inferInstance f)
    (hg : @Measurable Ω ℝ m inferInstance g) :
    @Measurable Ω ℝ m inferInstance (fun ω => f ω - g ω) :=
  hf.sub hg

lemma measurable_mul_σAlg {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : @Measurable Ω ℝ m inferInstance f)
    (hg : @Measurable Ω ℝ m inferInstance g) :
    @Measurable Ω ℝ m inferInstance (fun ω => f ω * g ω) :=
  hf.mul hg

lemma measurable_div_const_σAlg {m : MeasurableSpace Ω} {f : Ω → ℝ} (c : ℝ)
    (hf : @Measurable Ω ℝ m inferInstance f) :
    @Measurable Ω ℝ m inferInstance (fun ω => f ω / c) :=
  hf.div_const c

lemma measurable_mono_σAlg {m m' : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : @Measurable Ω ℝ m inferInstance f) (hle : m ≤ m') :
    @Measurable Ω ℝ m' inferInstance f :=
  hf.mono hle le_rfl

/-- Recursive grid wealth `X_n` is `F_{t_n}`-measurable. -/
lemma measurable_doublingX_adapted (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ n, Measurable[(pathFiltration B).σAlg (tGrid T n)]
      (doublingX (bmCoord B) T n)
  | 0 => by
    simp only [doublingX]
    exact measurable_const_σAlg (m := (pathFiltration B).σAlg (tGrid T 0)) 0
  | n + 1 => by
    have hX := measurable_doublingX_adapted B hT n
    have hX' : Measurable[(pathFiltration B).σAlg (tGrid T (n + 1))]
        (doublingX (bmCoord B) T n) :=
      measurable_mono_σAlg hX ((pathFiltration B).mono (tGrid_lt_succ hT n).le)
    have hC : Measurable[(pathFiltration B).σAlg (tGrid T (n + 1))]
        (doublingC (bmCoord B) T n) :=
      measurable_div_const_σAlg _
        (measurable_sub_σAlg
          (measurable_const_σAlg
            (m := (pathFiltration B).σAlg (tGrid T (n + 1))) 1)
          hX')
    have hE : MeasurableSet[(pathFiltration B).σAlg (tGrid T (n + 1))]
        (nonHitPrefix (bmCoord B) T n) :=
      (pathFiltration B).mono (tGrid_lt_succ hT n).le _
        ((nonHitPrefix_props B hT).1 n)
    have hBτ : Measurable[(pathFiltration B).σAlg (tGrid T (n + 1))]
        (fun ω => bmCoord B (tauHit (bmCoord B) T n ω) ω) :=
      measurable_bmCoord_eval_le B (tGrid_mem hT (n + 1))
        (isStoppingTime_tauHit B hT n)
        fun ω => (tauHit_mem_Icc hT (bmCoord B) n ω).2
    have hBt : Measurable[(pathFiltration B).σAlg (tGrid T (n + 1))]
        (bmCoord B (tGrid T n)) :=
      bmCoord_adapted (T := tGrid T (n + 1)) B
        ⟨(tGrid_mem hT n).1, (tGrid_lt_succ hT n).le⟩
    have hinc : Measurable[(pathFiltration B).σAlg (tGrid T (n + 1))] fun ω =>
        if ω ∈ nonHitPrefix (bmCoord B) T n then
          doublingC (bmCoord B) T n ω *
            (bmCoord B (tauHit (bmCoord B) T n ω) ω - bmCoord B (tGrid T n) ω)
        else 0 :=
      measurable_ite_σAlg
        (m := (pathFiltration B).σAlg (tGrid T (n + 1))) hE
        (measurable_mul_σAlg hC (measurable_sub_σAlg hBτ hBt))
        (measurable_const_σAlg
          (m := (pathFiltration B).σAlg (tGrid T (n + 1))) 0)
    have heq : doublingX (bmCoord B) T (n + 1) =
        fun ω => doublingX (bmCoord B) T n ω +
          (if ω ∈ nonHitPrefix (bmCoord B) T n then
            doublingC (bmCoord B) T n ω *
              (bmCoord B (tauHit (bmCoord B) T n ω) ω -
                bmCoord B (tGrid T n) ω)
           else 0) := by
      funext ω
      simp [doublingX, doublingC]
    rw [heq]
    exact measurable_add_σAlg hX' hinc

/-- The doubling weight `c_n` is `F_{t_n}`-measurable. -/
lemma measurable_doublingC_adapted (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Measurable[(pathFiltration B).σAlg (tGrid T n)]
      (doublingC (bmCoord B) T n) :=
  measurable_div_const_σAlg _
    (measurable_sub_σAlg
      (measurable_const_σAlg
        (m := (pathFiltration B).σAlg (tGrid T n)) 1)
      (measurable_doublingX_adapted B hT n))

/-- A left-open stopped block `f · 1_{(a, τ] ∩ (0, T]}` with `f` measurable at time `a`
is predictable. -/
lemma measurable_uncurry_stoppedBlock {σAlg : ℝ → MeasurableSpace Ω} {T a : ℝ}
    (hT : 0 < T) (ha0 : 0 ≤ a) (haT : a ≤ T) (τ : Ω → ℝ)
    (hτ : IsStoppingTimeOn σAlg T τ) {f : Ω → ℝ}
    (hf : Measurable[σAlg a] f) :
    Measurable[predSigma σAlg T]
      (fun p : ℝ × Ω =>
        if a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T then f p.2 else 0) := by
  intro s hs
  set I : Set (ℝ × Ω) := {p | a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T}
  have hI : MeasurableSet[predSigma σAlg T] I :=
    measurableSet_stochInterval hT ha0 haT τ hτ
  have hpre :
      (fun p : ℝ × Ω =>
        if a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T then f p.2 else 0) ⁻¹' s =
        (I ∩ (Ioc a T ×ˢ (f ⁻¹' s))) ∪
          (if 0 ∈ s then Iᶜ else (∅ : Set (ℝ × Ω))) := by
    ext p
    by_cases hpI : a < p.1 ∧ p.1 ≤ τ p.2 ∧ p.1 ≤ T
    · have hp : p ∈ I := hpI
      have hpIoc : p.1 ∈ Ioc a T := ⟨hpI.1, hpI.2.2⟩
      by_cases hfmem : f p.2 ∈ s
      · simp [hpI, hp, hpIoc, hfmem]
      · simp [hpI, hp, hpIoc, hfmem]
    · have hp : p ∉ I := hpI
      by_cases h0 : 0 ∈ s
      · simp [hpI, hp, h0]
      · simp [hpI, hp, h0]
  rw [hpre]
  have hrect : MeasurableSet[predSigma σAlg T] (Ioc a T ×ˢ (f ⁻¹' s)) :=
    measurableSet_predRect ha0 haT le_rfl (hf hs)
  have hite : MeasurableSet[predSigma σAlg T]
      (if 0 ∈ s then Iᶜ else (∅ : Set (ℝ × Ω))) := by
    by_cases h0 : 0 ∈ s
    · rw [ite_eq_left h0]
      exact hI.compl
    · rw [ite_eq_right h0]
      exact @MeasurableSet.empty (ℝ × Ω) (predSigma σAlg T)
  exact (hI.inter hrect).union hite

/-- The n-th doubling block, including the prefix indicator, is predictable. -/
lemma measurable_uncurry_doublingK_block (B : MultiBrownian Ω P 1) {T : ℝ}
    (hT : 0 < T) (n : ℕ) :
    Measurable[predSigma (pathFiltration B).σAlg T]
      (fun p : ℝ × Ω =>
        if p.2 ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < p.1 ∧
            p.1 ≤ tauHit (bmCoord B) T n p.2
          then doublingC (bmCoord B) T n p.2 else 0) := by
  have ha0 : 0 ≤ tGrid T n := (tGrid_mem hT n).1
  have haT : tGrid T n ≤ T := (tGrid_mem hT n).2
  have hf : Measurable[(pathFiltration B).σAlg (tGrid T n)]
      (fun ω =>
        if ω ∈ nonHitPrefix (bmCoord B) T n then
          doublingC (bmCoord B) T n ω else 0) :=
    measurable_ite_σAlg (m := (pathFiltration B).σAlg (tGrid T n))
      ((nonHitPrefix_props B hT).1 n)
      (measurable_doublingC_adapted B hT n)
      (measurable_const_σAlg
        (m := (pathFiltration B).σAlg (tGrid T n)) 0)
  have hblock :=
    measurable_uncurry_stoppedBlock hT ha0 haT
      (tauHit (bmCoord B) T n) (isStoppingTime_tauHit B hT n) hf
  have heq :
      (fun p : ℝ × Ω =>
        if p.2 ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < p.1 ∧
            p.1 ≤ tauHit (bmCoord B) T n p.2
          then doublingC (bmCoord B) T n p.2 else 0) =
        fun p =>
          if tGrid T n < p.1 ∧ p.1 ≤ tauHit (bmCoord B) T n p.2 ∧ p.1 ≤ T then
            (if p.2 ∈ nonHitPrefix (bmCoord B) T n then
              doublingC (bmCoord B) T n p.2 else 0)
          else 0 := by
    funext p
    by_cases hE : p.2 ∈ nonHitPrefix (bmCoord B) T n
    · by_cases hlt : tGrid T n < p.1
      · by_cases hτ : p.1 ≤ tauHit (bmCoord B) T n p.2
        · by_cases hsT : p.1 ≤ T
          · simp [hE, hlt, hτ, hsT]
          · have hτle : tauHit (bmCoord B) T n p.2 ≤ T :=
              (tauHit_mem_Icc hT (bmCoord B) n p.2).2.trans
                (tGrid_mem hT (n + 1)).2
            have : ¬ p.1 ≤ tauHit (bmCoord B) T n p.2 :=
              not_le.mpr (lt_of_le_of_lt hτle (not_le.mp hsT))
            exact (this hτ).elim
        · simp [hE, hlt, hτ]
      · simp [hE, hlt]
    · simp [hE]
  rwa [heq]

/-- If `s ∉ (0, T)`, no doubling block is live at time `s`. -/
lemma doublingK_term_eq_zero_outside_Ioo {T s : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ)
    (hs : s ∉ Ioo 0 T) (n : ℕ) (ω : Ω) :
    ¬ (ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω) := by
  intro hterm
  by_cases hpos : 0 < s
  · have hsT : ¬ s < T := fun hst => hs ⟨hpos, hst⟩
    have hleτ : ¬ s ≤ tauHit B T n ω := by
      have hτlt : tauHit B T n ω < T :=
        lt_of_le_of_lt (tauHit_mem_Icc hT B n ω).2 (tGrid_lt_T hT (n + 1))
      exact not_le.mpr (lt_of_lt_of_le hτlt (not_lt.mp hsT))
    exact hleτ hterm.2.2
  · have hlt : ¬ tGrid T n < s :=
      not_lt.mpr ((not_lt.mp hpos).trans (tGrid_mem hT n).1)
    exact hlt hterm.2.1

/-- If `s ∈ (0, T)` and `n` is past the unique live grid interval, the block vanishes. -/
lemma doublingK_term_eq_zero_of_nGrid_le {T s : ℝ} (hT : 0 < T)
    (hs0 : 0 < s) (hsT : s < T) (B : ℝ → Ω → ℝ) {n : ℕ}
    (hn : nGrid T s + 1 ≤ n) (ω : Ω) :
    ¬ (ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω) := by
  have hmono : tGrid T (nGrid T s + 1) ≤ tGrid T n := tGrid_mono hT hn
  exact fun hterm =>
    (not_lt.mpr ((nGrid_spec hT hs0 hsT).2.trans hmono)) hterm.2.1

/-- Partial sums of the doubling blocks converge pointwise to `doublingK`. -/
lemma tendsto_partial_doublingK {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) :
    Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0))
      atTop (𝓝 (doublingK B T s ω)) := by
  by_cases hs : s ∈ Ioo 0 T
  · have hsum : doublingK B T s ω =
        ∑ n ∈ Finset.range (nGrid T s + 1),
          (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0) :=
      doublingK_eq_sum_nGrid hT hs.1 hs.2 B ω
    refine tendsto_atTop_of_eventually_const (i₀ := nGrid T s + 1) fun N hN => ?_
    rw [hsum]
    exact (Finset.sum_subset (Finset.range_subset_range.mpr hN) fun n hnN hnG => by
      have hn : nGrid T s + 1 ≤ n := by
        simp only [Finset.mem_range, not_lt] at hnG
        exact hnG
      simp [doublingK_term_eq_zero_of_nGrid_le hT hs.1 hs.2 B hn ω]).symm
  · have h0 : doublingK B T s ω = 0 :=
      doublingK_eq_zero_of_not_mem_Ioo hT B hs ω
    have hterm : ∀ N,
        (∑ n ∈ Finset.range N,
          (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
            then doublingC B T n ω else 0)) = 0 := fun N =>
      Finset.sum_eq_zero fun n _ => by
        simp [doublingK_term_eq_zero_outside_Ioo hT B hs n ω]
    rw [h0]
    have hfun :
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
              then doublingC B T n ω else 0)) = fun _ => 0 :=
      funext hterm
    rw [hfun]
    exact tendsto_const_nhds

/-- The doubling integrand is predictable on `[0, T]`. -/
lemma isPredictableProcess_doublingK (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    IsPredictableProcess (pathFiltration B).σAlg T (doublingK (bmCoord B) T) := by
  let f : ℕ → ℝ × Ω → ℝ := fun N p =>
    ∑ n ∈ Finset.range N,
      (if p.2 ∈ nonHitPrefix (bmCoord B) T n ∧ tGrid T n < p.1 ∧
          p.1 ≤ tauHit (bmCoord B) T n p.2
        then doublingC (bmCoord B) T n p.2 else 0)
  have hf : ∀ N, Measurable[predSigma (pathFiltration B).σAlg T] (f N) :=
    fun N => Finset.measurable_fun_sum _ fun n _ =>
      measurable_uncurry_doublingK_block B hT n
  have hlim : Tendsto f atTop (𝓝 (Function.uncurry (doublingK (bmCoord B) T))) :=
    tendsto_pi_nhds.mpr fun p => tendsto_partial_doublingK hT (bmCoord B) p.1 p.2
  exact @measurable_of_tendsto_metrizable (ℝ × Ω) ℝ
    (predSigma (pathFiltration B).σAlg T) _ _ _ _ f
    (Function.uncurry (doublingK (bmCoord B) T)) hf hlim

/-- For each path, `s ↦ K_s(ω)` is Borel-measurable on `ℝ`. -/
lemma measurable_doublingK_slice {T : ℝ} (hT : 0 < T) (B : ℝ → Ω → ℝ) (ω : Ω) :
    Measurable (fun s : ℝ => doublingK B T s ω) := by
  let f : ℕ → ℝ → ℝ := fun N s =>
    ∑ n ∈ Finset.range N,
      (if ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧ s ≤ tauHit B T n ω
        then doublingC B T n ω else 0)
  have hf : ∀ N, Measurable (f N) := fun N =>
    Finset.measurable_fun_sum _ fun n _ => by
      have hset : MeasurableSet
          {s : ℝ | ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧
            s ≤ tauHit B T n ω} := by
        by_cases hE : ω ∈ nonHitPrefix B T n
        · have heq :
              {s : ℝ | ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧
                s ≤ tauHit B T n ω} =
              Ioc (tGrid T n) (tauHit B T n ω) := by
            ext s; simp [hE]
          rw [heq]
          exact measurableSet_Ioc
        · have heq :
              {s : ℝ | ω ∈ nonHitPrefix B T n ∧ tGrid T n < s ∧
                s ≤ tauHit B T n ω} = ∅ := by
            ext s; simp [hE]
          rw [heq]
          exact MeasurableSet.empty
      exact Measurable.ite hset measurable_const measurable_const
  exact measurable_of_tendsto_metrizable hf
    (tendsto_pi_nhds.mpr fun s => tendsto_partial_doublingK hT B s ω)

/-- Pathwise `∫₀ᵀ K_s² ds < ∞` upgrades to `IntegrableOn` of `K²` on `[0, T]`. -/
lemma integrableOn_doublingK_sq (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun s => doublingK (bmCoord B) T s ω ^ 2) (Icc 0 T) volume := by
  filter_upwards [doublingK_sq_int_finite_ae B hT] with ω hfin
  refine ⟨((measurable_doublingK_slice hT (bmCoord B) ω).pow_const 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have key : ∀ s, ‖(fun u => doublingK (bmCoord B) T u ω ^ 2) s‖ₑ =
      ENNReal.ofReal (doublingK (bmCoord B) T s ω ^ 2) := fun s =>
    Real.enorm_eq_ofReal (sq_nonneg _)
  convert hfin
  exact key _

/-- The doubling strategy is S-admissible for the constant coefficients `S = σ = 1`. -/
lemma sAdmissible_doublingK (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    SAdmissible (pathFiltration B).σAlg P
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) T
      (doublingK (bmCoord B) T) := by
  refine ⟨isPredictableProcess_doublingK B hT, ?_⟩
  filter_upwards [integrableOn_doublingK_sq B hT] with ω hInt
  simpa using hInt

/-- Literal NFLVR (no lower bound on wealth) fails for Brownian motion: the doubling
strategy is S-admissible, its terminal wealth is `1` almost surely, and this is a
non-trivial free lunch in the Delbaen–Schachermayer cone. -/
theorem theorem_literal_nflvr_fails (B : MultiBrownian Ω P 1) {T : ℝ} (hT : 0 < T) :
    ¬ SatisfiesNFLVR_DS P
        (LiteralGains (pathFiltration B).σAlg P (bmCoord B)
          (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) T) := by
  intro hNFLVR
  have hadm := sAdmissible_doublingK B hT
  have hIto : IsItoIntegral P (bmCoord B)
      (fun t ω => doublingK (bmCoord B) T t ω * (1 : ℝ) * (1 : ℝ))
      (doublingWealth (bmCoord B) T) T := by
    have heq : (fun t ω => doublingK (bmCoord B) T t ω * (1 : ℝ) * (1 : ℝ)) =
        doublingK (bmCoord B) T := by
      funext t ω; ring
    rw [heq]
    exact isItoIntegral_doublingWealth B hT
  have hG : (fun ω => doublingWealth (bmCoord B) T T ω) ∈
      LiteralGains (pathFiltration B).σAlg P (bmCoord B)
        (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) T :=
    ⟨doublingK (bmCoord B) T, doublingWealth (bmCoord B) T, hadm, hIto, rfl⟩
  have hone : (fun _ => (1 : ℝ)) ∈
      nflvrCone P
        (LiteralGains (pathFiltration B).σAlg P (bmCoord B)
          (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) T) := by
    refine ⟨memLp_const (p := ∞) (1 : ℝ),
      (fun ω => doublingWealth (bmCoord B) T T ω), hG,
      (fun _ => (0 : ℝ)), Eventually.of_forall fun _ => le_rfl, ?_⟩
    filter_upwards [doublingWealth_T_eq_one_ae B hT] with ω hω
    simp [hω]
  have hws : InWeakStarClosure P
      (nflvrCone P
        (LiteralGains (pathFiltration B).σAlg P (bmCoord B)
          (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) T))
      (fun _ => (1 : ℝ)) := by
    refine ⟨memLp_const (p := ∞) (1 : ℝ), fun ε hε gs _hgs => ?_⟩
    refine ⟨fun _ => (1 : ℝ), hone, memLp_const (p := ∞) (1 : ℝ), fun g _hg => ?_⟩
    have : |∫ ω, ((1 : ℝ) - 1) * g ω ∂P| = 0 := by
      simp
    simpa [this] using hε
  have hzero := hNFLVR (fun _ => (1 : ℝ))
    (Eventually.of_forall fun _ => zero_le_one) hws
  have huniv : {ω : Ω | (1 : ℝ) ≠ 0} = Set.univ := by
    ext ω; simp
  have hμ : P {ω : Ω | ¬ (1 : ℝ) = 0} = 0 := ae_iff.mp hzero
  rw [huniv, measure_univ] at hμ
  exact one_ne_zero hμ

end SignatureVolatility
