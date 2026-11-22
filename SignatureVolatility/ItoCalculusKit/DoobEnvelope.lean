module

public import SignatureVolatility.ItoCalculusKit.GBMEnvelope

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace SignatureVolatility

/-!
# A square-integrable envelope for a martingale with a continuous version

If `X` satisfies `X_q = 𝔼[X_T | 𝓕_q]` at the dyadic points of `[0, T]`, `X_T ∈ L²`, and on the
dyadic points `X` agrees almost surely with a process `X̃` with continuous paths on `[0, T]`,
then Doob's `L²` maximal inequality on the dyadic grids and Fatou give a measurable `L²` envelope
of `|X̃|` on all of `[0, T]` (`exists_envelope_of_dyadic_martingale`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Maximum of `|X|` over the level-`n` dyadic grid. -/
def gridMaxAbs (X : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    (fun j => ‖X (dyadicGrid T n j) ω‖)

lemma measurable_gridMaxAbs {X : ℝ → Ω → ℝ} (hX : ∀ t, Measurable (X t)) (T : ℝ) (n : ℕ) :
    Measurable (gridMaxAbs X T n) := by
  have h := Finset.measurable_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
    (f := fun j ω => ‖X (dyadicGrid T n j) ω‖) fun j _ => (hX _).norm
  convert h using 1
  funext ω
  rw [Finset.sup'_apply]
  rfl

omit [MeasurableSpace Ω] in
lemma le_gridMaxAbs (X : ℝ → Ω → ℝ) (T : ℝ) {n j : ℕ} (hj : j ≤ 2 ^ n) (ω : Ω) :
    ‖X (dyadicGrid T n j) ω‖ ≤ gridMaxAbs X T n ω :=
  Finset.le_sup' (f := fun j => ‖X (dyadicGrid T n j) ω‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

omit [MeasurableSpace Ω] in
lemma gridMaxAbs_nonneg (X : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : 0 ≤ gridMaxAbs X T n ω :=
  (norm_nonneg _).trans (le_gridMaxAbs X T (Nat.zero_le _) ω)

omit [MeasurableSpace Ω] in
lemma gridMaxAbs_mono (X : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun n => gridMaxAbs X T n ω := by
  refine monotone_nat_of_le_succ fun n => Finset.sup'_le _ _ fun j hj => ?_
  have hj' : j ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← dyadicGrid_succ hj']
  exact le_gridMaxAbs X T (by rw [pow_succ]; omega) ω

lemma dyadicGrid_le {T : ℝ} (hT : 0 ≤ T) (n j : ℕ) : dyadicGrid T n j ≤ T := by
  calc dyadicGrid T n j ≤ dyadicGrid T n (max j (2 ^ n)) := dyadicGrid_mono hT n (le_max_left _ _)
    _ = T := by
        unfold dyadicGrid
        rw [min_eq_right (le_max_right _ _)]
        push_cast
        field_simp

lemma dyadicGrid_mem {T : ℝ} (hT : 0 ≤ T) (n j : ℕ) : dyadicGrid T n j ∈ Icc 0 T :=
  ⟨dyadicGrid_nonneg hT n j, dyadicGrid_le hT n j⟩

/-- Every `t ∈ [0, T]` is a limit of dyadic points of `[0, T]`. -/
lemma exists_dyadic_tendsto {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ j : ℕ → ℕ, (∀ n, j n ≤ 2 ^ n) ∧
      Tendsto (fun n => dyadicGrid T n (j n)) atTop (𝓝 t) := by
  set j : ℕ → ℕ := fun n => ⌊t * 2 ^ n / T⌋₊ with hj
  have hjle : ∀ n, j n ≤ 2 ^ n := fun n => by
    refine Nat.floor_le_of_le ?_
    rw [div_le_iff₀ hT]
    push_cast
    nlinarith [ht.2, pow_pos (two_pos : (0 : ℝ) < 2) n]
  have hgrid : ∀ n, dyadicGrid T n (j n) = (j n : ℝ) * (T / 2 ^ n) := fun n => by
    simp only [dyadicGrid, min_eq_left (hjle n)]
  have hlo : ∀ n, t - T / 2 ^ n ≤ dyadicGrid T n (j n) := fun n => by
    rw [hgrid]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have h := Nat.lt_floor_add_one (t * 2 ^ n / T)
    have : t * 2 ^ n / T - 1 ≤ (j n : ℝ) := by simp only [hj]; linarith
    calc t - T / 2 ^ n = (t * 2 ^ n / T - 1) * (T / 2 ^ n) := by field_simp
      _ ≤ (j n : ℝ) * (T / 2 ^ n) :=
          mul_le_mul_of_nonneg_right this (by positivity)
  have hhi : ∀ n, dyadicGrid T n (j n) ≤ t := fun n => by
    rw [hgrid]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have h := Nat.floor_le (show 0 ≤ t * 2 ^ n / T by have := ht.1; positivity)
    calc (j n : ℝ) * (T / 2 ^ n) ≤ (t * 2 ^ n / T) * (T / 2 ^ n) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = t := by field_simp
  have hTn : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul T
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  refine ⟨j, hjle, tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlo hhi⟩
  simpa using tendsto_const_nhds.sub hTn

/-- **Doob envelope from a dyadic martingale with a continuous version.** -/
theorem exists_envelope_of_dyadic_martingale (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    {X Xt : ℝ → Ω → ℝ} (hXm : ∀ t, Measurable (X t))
    (hX : ∀ n j, X (dyadicGrid T n j) =ᵐ[P]
      P[X T | (pathFiltration B).σAlg (dyadicGrid T n j)])
    (hL2 : MemLp (X T) 2 P)
    (hXt : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xt t ω) (Icc 0 T) ∧
      ∀ n j, X (dyadicGrid T n j) ω = Xt (dyadicGrid T n j) ω) :
    ∃ E : Ω → ℝ, Measurable E ∧ (∀ ω, 0 ≤ E ω) ∧ MemLp E 2 P ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |Xt t ω| ≤ E ω := by
  set E : Ω → ℝ := fun ω => ⨆ n, gridMaxAbs X T n ω with hE
  have hEm : Measurable E := Measurable.iSup fun n => measurable_gridMaxAbs hXm T n
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω => Real.iSup_nonneg fun n => gridMaxAbs_nonneg X T n ω
  have hbdd : ∀ᵐ ω ∂P, BddAbove (Set.range fun n => gridMaxAbs X T n ω) := by
    filter_upwards [hXt] with ω ⟨hc, heq⟩
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hc
    refine ⟨K, ?_⟩
    rintro _ ⟨n, rfl⟩
    refine Finset.sup'_le _ _ fun j _ => ?_
    rw [heq n j]
    exact hK _ (dyadicGrid_mem hT.le n j)
  have htend : ∀ᵐ ω ∂P, Tendsto (fun n => gridMaxAbs X T n ω) atTop (𝓝 (E ω)) := by
    filter_upwards [hbdd] with ω hω
    exact tendsto_atTop_ciSup (gridMaxAbs_mono X T ω) hω
  have hbound : ∀ n, eLpNorm (gridMaxAbs X T n) 2 P ≤ 2 * eLpNorm (X T) 2 P := by
    intro n
    set F := dyadicFiltration B hT.le n
    have hmart := martingale_condExp (X T) F P
    have h := hmart.eLpNorm_norm_runMax_le one_lt_two (2 ^ n)
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h3 : ENNReal.ofReal (2 / (2 - 1)) = 2 := by norm_num
    rw [h2, h3] at h
    have hae : gridMaxAbs X T n =ᵐ[P] fun ω => (Finset.range (2 ^ n + 1)).sup'
        Finset.nonempty_range_add_one (fun k => ‖(P[X T | F k]) ω‖) := by
      filter_upwards [ae_all_iff.2 fun j => hX n j] with ω hω
      unfold gridMaxAbs
      refine Finset.sup'_congr _ rfl fun j _ => ?_
      rw [hω j]
      rfl
    rw [eLpNorm_congr_ae hae]
    refine h.trans ?_
    gcongr
    exact eLpNorm_condExp_le_eLpNorm _ one_le_two
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := P)
    (fun n => (measurable_gridMaxAbs hXm T n).aestronglyMeasurable) E
    hEm.aestronglyMeasurable htend
  have hlt : eLpNorm E 2 P < ∞ :=
    lt_of_le_of_lt (hfat.trans (liminf_le_of_frequently_le'
      (Eventually.frequently (Eventually.of_forall hbound))))
      (ENNReal.mul_lt_top (by norm_num) hL2.eLpNorm_lt_top)
  have hEL : MemLp E 2 P := hlt
  refine ⟨E, hEm, hE0, hEL, ?_⟩
  filter_upwards [hXt, hbdd] with ω ⟨hc, heq⟩ hω
  intro t ht
  obtain ⟨j, hjle, hconv⟩ := exists_dyadic_tendsto hT ht
  have hconv' : Tendsto (fun n => dyadicGrid T n (j n)) atTop (𝓝[Icc 0 T] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hconv, Eventually.of_forall fun n => dyadicGrid_mem hT.le n _⟩
  have hlim := ((hc t ht).tendsto.comp hconv').abs
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [← heq n (j n), ← Real.norm_eq_abs]
  exact (le_gridMaxAbs X T (hjle n) ω).trans (le_ciSup hω n)

end SignatureVolatility
