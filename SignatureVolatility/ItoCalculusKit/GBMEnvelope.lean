module

public import MathFin.Probability.Discrete.DoobLpMaximalInequality
public import SignatureVolatility.ItoCalculusKit.GBMMartingale


@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace SignatureVolatility

/-!
# A square-integrable envelope for geometric Brownian motion on `[0, T]`

Sampling `gbm` on the dyadic grid of `[0, T]` with `2ⁿ` cells gives a discrete martingale
(`condExp_gbm`), so Doob's `L²` maximal inequality bounds the grid maximum by `2 ‖gbm_T‖₂`
uniformly in `n`. The grids are nested, so the grid maxima increase to a measurable envelope
`gbmEnvelope`; Fatou puts it in `L²`, and path continuity makes it dominate `gbm_t` for every
`t ∈ [0, T]` (`exists_gbm_envelope`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Dyadic grid of `[0, T]` with `2ⁿ` cells, frozen at `T` after the last point. -/
def dyadicGrid (T : ℝ) (n j : ℕ) : ℝ := ((min j (2 ^ n) : ℕ) : ℝ) * (T / 2 ^ n)

lemma dyadicGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (n j : ℕ) : 0 ≤ dyadicGrid T n j := by
  unfold dyadicGrid; positivity

lemma dyadicGrid_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (dyadicGrid T n) := by
  intro i j hij
  unfold dyadicGrid
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_min_right _ hij) (by positivity)

lemma dyadicGrid_last (T : ℝ) (n : ℕ) : dyadicGrid T n (2 ^ n) = T := by
  unfold dyadicGrid
  rw [min_self]
  push_cast
  field_simp

lemma dyadicGrid_succ {T : ℝ} {n j : ℕ} (hj : j ≤ 2 ^ n) :
    dyadicGrid T (n + 1) (2 * j) = dyadicGrid T n j := by
  unfold dyadicGrid
  rw [min_eq_left hj, min_eq_left (by rw [pow_succ]; omega)]
  push_cast
  field_simp
  ring

/-- The path filtration sampled along the dyadic grid. -/
def dyadicFiltration (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq j := (pathFiltration B).σAlg (dyadicGrid T n j)
  mono' _ _ hij := (pathFiltration B).mono (dyadicGrid_mono hT n hij)
  le' _ := (pathFiltration B).le_ambient _

lemma martingale_gbm_dyadic (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (n : ℕ) :
    Martingale (fun j => gbm B k c (dyadicGrid T n j)) (dyadicFiltration B hT n) P :=
  ⟨fun j => (measurable_gbm_pathFiltration B k c (dyadicGrid_nonneg hT n j)).stronglyMeasurable,
    fun i _ hij => condExp_gbm B k c (dyadicGrid_nonneg hT n i) (dyadicGrid_mono hT n hij)⟩

/-- Maximum of `|gbm|` over the level-`n` dyadic grid. -/
def gbmGridMax (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    (fun j => ‖gbm B k c (dyadicGrid T n j) ω‖)

lemma measurable_gbmGridMax (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) (n : ℕ) :
    Measurable (gbmGridMax B k c T n) := by
  have h := Finset.measurable_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
    (f := fun j ω => ‖gbm B k c (dyadicGrid T n j) ω‖) fun j _ => (measurable_gbm B k c _).norm
  convert h using 1
  funext ω
  rw [Finset.sup'_apply]
  rfl

lemma le_gbmGridMax (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) {n j : ℕ} (hj : j ≤ 2 ^ n)
    (ω : Ω) : gbm B k c (dyadicGrid T n j) ω ≤ gbmGridMax B k c T n ω :=
  (Real.le_norm_self _).trans (Finset.le_sup' (f := fun j => ‖gbm B k c (dyadicGrid T n j) ω‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

lemma gbmGridMax_mono (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) (ω : Ω) :
    Monotone fun n => gbmGridMax B k c T n ω := by
  refine monotone_nat_of_le_succ fun n => Finset.sup'_le _ _ fun j hj => ?_
  have hj' : j ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← dyadicGrid_succ hj', Real.norm_of_nonneg (gbm_pos B k c _ ω).le]
  exact le_gbmGridMax B k c T (by rw [pow_succ]; omega) ω

lemma continuous_gbm_path (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) (ω : Ω) :
    Continuous fun t => gbm B k c t ω := by
  unfold gbm
  exact Real.continuous_exp.comp ((continuous_const.mul
    ((B.pathContinuous k ω).comp continuous_real_toNNReal)).sub
    (continuous_const.mul continuous_id))

lemma bddAbove_gbmGridMax (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (ω : Ω) : BddAbove (Set.range fun n => gbmGridMax B k c T n ω) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image
    (continuous_gbm_path B k c ω).continuousOn
  refine ⟨K, ?_⟩
  rintro _ ⟨n, rfl⟩
  refine Finset.sup'_le _ _ fun j _ => ?_
  rw [Real.norm_of_nonneg (gbm_pos B k c _ ω).le]
  refine hK (mem_image_of_mem _ ⟨dyadicGrid_nonneg hT n j, ?_⟩)
  calc dyadicGrid T n j ≤ dyadicGrid T n (max j (2 ^ n)) := dyadicGrid_mono hT n (le_max_left _ _)
    _ = T := by
        unfold dyadicGrid
        rw [min_eq_right (le_max_right _ _)]
        push_cast
        field_simp

/-- The dyadic envelope `supₙ maxⱼ |gbm (j T / 2ⁿ)|`. -/
def gbmEnvelope (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) (ω : Ω) : ℝ :=
  ⨆ n, gbmGridMax B k c T n ω

lemma measurable_gbmEnvelope (B : MultiBrownian Ω P d) (k : Fin d) (c T : ℝ) :
    Measurable (gbmEnvelope B k c T) :=
  Measurable.iSup fun n => measurable_gbmGridMax B k c T n

lemma tendsto_gbmGridMax (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (ω : Ω) : Tendsto (fun n => gbmGridMax B k c T n ω) atTop (𝓝 (gbmEnvelope B k c T ω)) :=
  tendsto_atTop_ciSup (gbmGridMax_mono B k c T ω) (bddAbove_gbmGridMax B k c hT ω)

lemma memLp_gbm_two (B : MultiBrownian Ω P d) (k : Fin d) (c t : ℝ) :
    MemLp (gbm B k c t) 2 P := by
  refine (memLp_two_iff_integrable_sq (measurable_gbm B k c t).aestronglyMeasurable).mpr ?_
  have h := (integrable_exp_mul_Wnn B k (2 * c) (Real.toNNReal t)).mul_const
    (Real.exp (-(c ^ 2 * t)))
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [gbm, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Doob envelope.** The dyadic envelope of geometric Brownian motion is in `L²`. -/
lemma memLp_gbmEnvelope (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (gbmEnvelope B k c T) 2 P := by
  have hbound : ∀ n, eLpNorm (gbmGridMax B k c T n) 2 P ≤ 2 * eLpNorm (gbm B k c T) 2 P := by
    intro n
    have h := (martingale_gbm_dyadic B k c hT n).eLpNorm_norm_runMax_le one_lt_two (2 ^ n)
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h3 : ENNReal.ofReal (2 / (2 - 1)) = 2 := by norm_num
    rw [h2, h3, dyadicGrid_last] at h
    exact h
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := P)
    (fun n => (measurable_gbmGridMax B k c T n).aestronglyMeasurable) (gbmEnvelope B k c T)
    (measurable_gbmEnvelope B k c T).aestronglyMeasurable
    (ae_of_all _ fun ω => tendsto_gbmGridMax B k c hT ω)
  have hlt : eLpNorm (gbmEnvelope B k c T) 2 P < ∞ :=
    lt_of_le_of_lt (hfat.trans (liminf_le_of_frequently_le'
      (Eventually.frequently (Eventually.of_forall hbound))))
      (ENNReal.mul_lt_top (by norm_num) (memLp_gbm_two B k c T).eLpNorm_lt_top)
  exact hlt

/-- The dyadic envelope dominates geometric Brownian motion at every time of `[0, T]`. -/
lemma gbm_le_gbmEnvelope (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 T) : gbm B k c t ω ≤ gbmEnvelope B k c T ω := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · -- `T = 0`: `t = 0` is the grid point `0`
    have ht0 : t = 0 := le_antisymm (hT0 ▸ ht.2) ht.1
    have h0 : dyadicGrid T 0 0 = t := by simp [dyadicGrid, ht0]
    rw [← h0]
    exact (le_gbmGridMax B k c T (Nat.zero_le _) ω).trans
      (le_ciSup (bddAbove_gbmGridMax B k c hT ω) 0)
  · -- approximate `t` from below by dyadic points
    set j : ℕ → ℕ := fun n => ⌊t * 2 ^ n / T⌋₊ with hj
    have hjle : ∀ n, j n ≤ 2 ^ n := fun n => by
      refine Nat.floor_le_of_le ?_
      rw [div_le_iff₀ hTpos]
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
    have hconv : Tendsto (fun n => dyadicGrid T n (j n)) atTop (𝓝 t) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlo hhi
      simpa using tendsto_const_nhds.sub hTn
    have hlim := ((continuous_gbm_path B k c ω).tendsto t).comp hconv
    refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    exact (le_gbmGridMax B k c T (hjle n) ω).trans
      (le_ciSup (bddAbove_gbmGridMax B k c hT ω) n)

/-- **Square-integrable envelope for geometric Brownian motion on `[0, T]`.** -/
theorem exists_gbm_envelope (B : MultiBrownian Ω P d) (k : Fin d) (c : ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ ω, ∀ t ∈ Icc 0 T, gbm B k c t ω ≤ G ω) ∧
      Integrable (fun ω => G ω ^ 2) P :=
  ⟨gbmEnvelope B k c T, measurable_gbmEnvelope B k c T,
    fun ω _ ht => gbm_le_gbmEnvelope B k c hT ω ht, (memLp_gbmEnvelope B k c hT).integrable_sq⟩

end SignatureVolatility
