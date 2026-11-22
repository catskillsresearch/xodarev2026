module

public import MathFin.Probability.Discrete.DoobLpMaximalInequality
public import SignatureVolatility.ItoCalculusKit.QVTransform

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace SignatureVolatility

/-!
# Doob bound for the raw Itô limit on all uniform grids

* `condExp_kitItoIntRaw`: `E[I_v | 𝓕_u] = I_u`;
* `ae_bdd_kitItoIntRaw_grid`: almost surely `sup_{N ≥ 1, i ≤ N} |I_{i t / N}| < ∞`, by Doob's
  `L²` maximal inequality on the nested grids `j t / m!`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The grid `j t / m!`, frozen at `t` after `j = m!`. -/
noncomputable def factGrid (t : ℝ) (m j : ℕ) : ℝ :=
  ((min j m.factorial : ℕ) : ℝ) * (t / (m.factorial : ℝ))

lemma factGrid_nonneg {t : ℝ} (ht : 0 ≤ t) (m j : ℕ) : 0 ≤ factGrid t m j := by
  unfold factGrid; positivity

lemma factGrid_mono {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : Monotone (factGrid t m) := by
  intro i j hij
  unfold factGrid
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_min_right _ hij) (by positivity)

lemma factGrid_le {t : ℝ} (ht : 0 ≤ t) (m j : ℕ) : factGrid t m j ≤ t := by
  unfold factGrid
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  calc ((min j m.factorial : ℕ) : ℝ) * (t / (m.factorial : ℝ))
      ≤ (m.factorial : ℝ) * (t / (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by positivity)
    _ = t := by field_simp

lemma factGrid_last (t : ℝ) (m : ℕ) : factGrid t m m.factorial = t := by
  unfold factGrid
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [min_self]; field_simp

lemma factGrid_of_le (t : ℝ) {m j : ℕ} (hj : j ≤ m.factorial) :
    factGrid t m j = (j : ℝ) * (t / (m.factorial : ℝ)) := by
  unfold factGrid; rw [min_eq_left hj]

section Doob

variable (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- **Martingale property of the raw Itô limit.** -/
theorem condExp_kitItoIntRaw (hd : 0 < d) (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvt : v ≤ t) :
    P[kitItoIntRaw B H v | (pathFiltration B).σAlg u] =ᵐ[P] kitItoIntRaw B H u := by
  have hv := hu.trans huv
  have hIv := (kitItoIntRaw_of_holderAdapted B hd hv (hH.mono hvt)).2.2
  have hIu := (kitItoIntRaw_of_holderAdapted B hd hu (hH.mono (huv.trans hvt))).2.2
  have hIum : Measurable[(pathFiltration B).σAlg u] (kitItoIntRaw B H u) :=
    measurable_kitItoIntRaw_path B H hu fun r hr0 hr =>
      (hH.meas r hr0 (hr.trans (huv.trans hvt))).mono ((pathFiltration B).mono hr) le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration B).le_ambient u) hIv
    (fun s _ _ => hIu.integrableOn) (fun s hs _ => ?_) hIum.aestronglyMeasurable).symm
  have hsa : MeasurableSet s := (pathFiltration B).le_ambient u _ hs
  set ind : Ω → ℝ := s.indicator fun _ => (1 : ℝ) with hinddef
  have hg : Measurable[(pathFiltration B).σAlg u] ind := measurable_const.indicator hs
  have hg2 : MemLp ind 2 P :=
    MemLp.of_bound (hg.mono ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by by_cases h : ω ∈ s <;> simp [hinddef, h])
  have h0 := integral_mul_kitItoIntRaw_sub_eq_zero B hd hH hu huv hvt hg hg2
  have hpt : ∀ f : Ω → ℝ, (fun ω => ind ω * f ω) = s.indicator f := fun f => by
    funext ω; by_cases h : ω ∈ s <;> simp [hinddef, h]
  have hind : ∀ f : Ω → ℝ, ∫ ω in s, f ω ∂P = ∫ ω, ind ω * f ω ∂P := fun f => by
    rw [hpt f, integral_indicator hsa]
  have hint : ∀ f : Ω → ℝ, Integrable f P → Integrable (fun ω => ind ω * f ω) P :=
    fun f hf => by rw [hpt f]; exact hf.indicator hsa
  rw [hind, hind]
  have h1 : ∫ ω, ind ω * (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ∂P =
      ∫ ω, ind ω * kitItoIntRaw B H v ω ∂P - ∫ ω, ind ω * kitItoIntRaw B H u ω ∂P := by
    rw [← integral_sub (hint _ hIv) (hint _ hIu)]
    congr 1; funext ω; ring
  linarith

/-- The path filtration sampled along the grid `j t / m!`. -/
noncomputable def factFiltration (ht : 0 ≤ t) (m : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq j := (pathFiltration B).σAlg (factGrid t m j)
  mono' _ _ hij := (pathFiltration B).mono (factGrid_mono ht m hij)
  le' _ := (pathFiltration B).le_ambient _

lemma martingale_kitItoIntRaw_fact (hd : 0 < d) (hH : HolderAdapted B H t K) (ht : 0 ≤ t) (m : ℕ) :
    Martingale (fun j => kitItoIntRaw B H (factGrid t m j)) (factFiltration B ht m) P := by
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · exact (measurable_kitItoIntRaw_path B H (factGrid_nonneg ht m j) fun r hr0 hr =>
      (hH.meas r hr0 (hr.trans (factGrid_le ht m j))).mono ((pathFiltration B).mono hr)
        le_rfl).stronglyMeasurable
  · exact condExp_kitItoIntRaw B hd hH (factGrid_nonneg ht m i) (factGrid_mono ht m hij)
      (factGrid_le ht m j)

/-- Maximum of `|I|` over the grid `j t / m!`. -/
noncomputable def kitGridMax (H : ℝ → Ω → ℝ) (t : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (range (m.factorial + 1)).sup' nonempty_range_add_one
    (fun j => ‖kitItoIntRaw B H (factGrid t m j) ω‖)

lemma le_kitGridMax (m : ℕ) {j : ℕ} (hj : j ≤ m.factorial) (ω : Ω) :
    ‖kitItoIntRaw B H (factGrid t m j) ω‖ ≤ kitGridMax B H t m ω :=
  le_sup' (f := fun j => ‖kitItoIntRaw B H (factGrid t m j) ω‖)
    (mem_range.mpr (Nat.lt_succ_of_le hj))

lemma kitGridMax_nonneg (m : ℕ) (ω : Ω) : 0 ≤ kitGridMax B H t m ω :=
  (norm_nonneg _).trans (le_kitGridMax B m (Nat.zero_le _) ω)

lemma kitGridMax_mono (ω : Ω) : Monotone fun m => kitGridMax B H t m ω := by
  refine monotone_nat_of_le_succ fun m => sup'_le _ _ fun j hj => ?_
  have hj' : j ≤ m.factorial := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hle : j * (m + 1) ≤ (m + 1).factorial := by
    rw [Nat.factorial_succ, mul_comm]; exact Nat.mul_le_mul_left _ hj'
  have he : factGrid t m j = factGrid t (m + 1) (j * (m + 1)) := by
    rw [factGrid_of_le t hj', factGrid_of_le t hle, Nat.factorial_succ]
    have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    push_cast
    field_simp
  rw [he]
  exact le_kitGridMax B (m + 1) hle ω

lemma measurable_kitGridMax (hH : HolderAdapted B H t K) (ht : 0 ≤ t) (m : ℕ) :
    Measurable (kitGridMax B H t m) := by
  have h := Finset.measurable_sup' (nonempty_range_add_one (n := m.factorial))
    (f := fun j ω => ‖kitItoIntRaw B H (factGrid t m j) ω‖) fun j _ =>
      ((measurable_kitItoIntRaw_path B H (factGrid_nonneg ht m j) fun r hr0 hr =>
        (hH.meas r hr0 (hr.trans (factGrid_le ht m j))).mono ((pathFiltration B).mono hr)
          le_rfl).mono ((pathFiltration B).le_ambient _) le_rfl).norm
  convert h using 1
  funext ω
  rw [Finset.sup'_apply]
  rfl

/-- **Grid boundedness of the raw Itô limit.** Almost surely, `|I_{i t / N}|` is bounded over all
`N ≥ 1` and `i ≤ N`. -/
theorem ae_bdd_kitItoIntRaw_grid (hd : 0 < d) (hH : HolderAdapted B H t K) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ N : ℕ, 0 < N → ∀ i ≤ N,
      |kitItoIntRaw B H ((i : ℝ) * (t / (N : ℝ))) ω| ≤ M := by
  set C : ℝ≥0∞ := 2 * eLpNorm (kitItoIntRaw B H t) 2 P with hC
  have hCt : C < ∞ := ENNReal.mul_lt_top (by norm_num)
    (((kitItoIntRaw_of_holderAdapted B hd ht hH).2.1.mono_exponent (p := 2)
      (by norm_num)).eLpNorm_lt_top)
  have hbound : ∀ m, eLpNorm (kitGridMax B H t m) 2 P ≤ C := by
    intro m
    have h := (martingale_kitItoIntRaw_fact B hd hH ht m).eLpNorm_norm_runMax_le one_lt_two
      m.factorial
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h3 : ENNReal.ofReal (2 / (2 - 1)) = 2 := by norm_num
    rw [h2, h3, factGrid_last] at h
    exact h
  have hlin : ∀ m, ∫⁻ ω, ENNReal.ofReal (kitGridMax B H t m ω ^ 2) ∂P ≤ C ^ 2 := by
    intro m
    have he := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P)
      (p := 2) two_ne_zero ENNReal.ofNat_ne_top
      (measurable_kitGridMax B hH ht m).aestronglyMeasurable
    have hpt : ∀ ω, ‖kitGridMax B H t m ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) =
        ENNReal.ofReal (kitGridMax B H t m ω ^ 2) := by
      intro ω
      rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofNat,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    simp_rw [hpt] at he
    have hL : ∫⁻ ω, ENNReal.ofReal (kitGridMax B H t m ω ^ 2) ∂P =
        eLpNorm (kitGridMax B H t m) 2 P ^ 2 := by
      rw [he, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hL]
    exact pow_le_pow_left₀ zero_le (hbound m) 2
  set F : Ω → ℝ≥0∞ := fun ω => ⨆ m, ENNReal.ofReal (kitGridMax B H t m ω ^ 2) with hF
  have hmeasF : ∀ m, Measurable fun ω => ENNReal.ofReal (kitGridMax B H t m ω ^ 2) := fun m =>
    ENNReal.measurable_ofReal.comp ((measurable_kitGridMax B hH ht m).pow_const 2)
  have hmonoF : Monotone fun m ω => ENNReal.ofReal (kitGridMax B H t m ω ^ 2) := by
    intro m n hmn ω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (kitGridMax_nonneg B m ω)
      (kitGridMax_mono B ω hmn) 2)
  have hFint : ∫⁻ ω, F ω ∂P ≤ C ^ 2 := by
    rw [hF, lintegral_iSup hmeasF hmonoF]
    exact iSup_le hlin
  have hFae : ∀ᵐ ω ∂P, F ω < ∞ :=
    ae_lt_top (Measurable.iSup hmeasF) (ne_top_of_le_ne_top (ENNReal.pow_ne_top hCt.ne) hFint)
  filter_upwards [hFae] with ω hω
  refine ⟨Real.sqrt (F ω).toReal, fun N hN i hi => ?_⟩
  set j := i * (N - 1).factorial with hj
  have hjN : j ≤ N.factorial := by
    rw [hj, ← Nat.mul_factorial_pred hN.ne']
    exact Nat.mul_le_mul_right _ hi
  have hgrid : (i : ℝ) * (t / (N : ℝ)) = factGrid t N j := by
    rw [factGrid_of_le t hjN, hj, ← Nat.mul_factorial_pred hN.ne']
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hf : ((N - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (N - 1).factorial_ne_zero
    push_cast
    field_simp
  rw [hgrid]
  have h1 : |kitItoIntRaw B H (factGrid t N j) ω| ≤ kitGridMax B H t N ω :=
    le_kitGridMax B N hjN ω
  have h2 : ENNReal.ofReal (kitGridMax B H t N ω ^ 2) ≤ F ω :=
    le_iSup (fun m => ENNReal.ofReal (kitGridMax B H t m ω ^ 2)) N
  have h3 : kitGridMax B H t N ω ^ 2 ≤ (F ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hω.ne).mp h2
  have h4 := Real.abs_le_sqrt h3
  rw [abs_of_nonneg (kitGridMax_nonneg B N ω)] at h4
  exact h1.trans h4

end Doob

end SignatureVolatility
