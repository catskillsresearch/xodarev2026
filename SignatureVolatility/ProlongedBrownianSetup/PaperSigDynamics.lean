module

public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ItoCalculusKit.CrossVariation

@[expose] public section

noncomputable section


open MeasureTheory Filter Topology Set

namespace SignatureVolatility

/-!
# Signature dynamics `dŴ = Ŵ ⊗ ∘dX` for the Brownian Stratonovich signature

Trapezoid (Stratonovich) Riemann sums of a coordinate `⟨e_I, Ŵ_{0,·}⟩` against `X^j` converge
in probability to `⟨e_{I j}, Ŵ_{0,t}⟩`. With `K = I.reverse`, `⟨e_I, Ŵ⟩ = Σ_{(c,J)} c · I^J`
over the contraction list of `K`, and `(I ++ [j]).reverse = j :: K`.

* time letter: trapezoid sums of continuous paths converge to the Lebesgue integral, and
  `I^{0 J}_t = ∫_0^t I^J_s ds` almost surely;
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Time letter -/

/-- Trapezoid sums against the time coordinate converge to the integral (continuous paths). -/
theorem tendsto_trapezoid_time {t : ℝ} (ht : 0 ≤ t) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 t)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      (1 / 2 : ℝ) * (y (k * t / (n + 1)) + y ((k + 1) * t / (n + 1))) *
        ((k + 1) * t / (n + 1) - k * t / (n + 1))) atTop (𝓝 (∫ s in (0 : ℝ)..t, y s)) := by
  have hL := tendsto_lebRiemann_of_continuousOn ht hy
  have hh : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hR := hL.add (hh.const_mul (y t - y 0))
  rw [mul_zero, add_zero] at hR
  have h := (hL.add hR).const_mul (1 / 2 : ℝ)
  rw [show (1 / 2 : ℝ) * ((∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, y s) =
    ∫ s in (0 : ℝ)..t, y s by ring] at h
  refine h.congr fun n => ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  set f : ℕ → ℝ := fun j => y ((j : ℝ) * (t / ((n : ℝ) + 1))) * (t / ((n : ℝ) + 1)) with hf
  have hsum : ∑ j ∈ Finset.range (n + 1), f (j + 1) =
      ∑ j ∈ Finset.range (n + 1), f j + (y t - y 0) * (t / ((n : ℝ) + 1)) := by
    have h1 := Finset.sum_range_succ' f (n + 1)
    have h2 := Finset.sum_range_succ f (n + 1)
    have hfN : f (n + 1) = y t * (t / ((n : ℝ) + 1)) := by
      simp only [hf]; push_cast; rw [mul_div_cancel₀ _ hn.ne']
    have hf0 : f 0 = y 0 * (t / ((n : ℝ) + 1)) := by simp [hf]
    rw [hfN] at h2; rw [hf0] at h1
    linarith
  rw [← hsum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hf]
  push_cast
  rw [show (k : ℝ) * t / (n + 1) = k * (t / (n + 1)) by ring,
    show ((k : ℝ) + 1) * t / (n + 1) = (k + 1) * (t / (n + 1)) by ring]
  ring

/-- Almost surely, `I^{0 J}_t = ∫_0^t I^J_s ds` for every word `J`. -/
lemma ae_itoWordIntegral_time_cons (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ J : Word (d + 1), itoWordIntegral B 0 t ω ((0 : Fin (d + 1)) :: J) =
      ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω J := by
  filter_upwards [ae_continuousOn_itoWordIntegral B ht] with ω hω J
  by_cases hJ : J = []
  · subst hJ; simp [itoWordIntegral_time, itoWordIntegral_empty]
  simp only [itoWordIntegral.eq_2, hJ, ↓reduceIte]
  have hj : ((0 : Fin (d + 1)) : ℕ) = 0 := rfl
  set X : ℝ → Ω → ℝ := fun u ω' => itoWordIntegral B 0 u ω' J
  have hstep : ∀ u, 0 ≤ u → u ≤ t →
      itoWordStep B 0 X 0 u ω = ∫ s in (0 : ℝ)..u, X s ω := by
    intro u hu hut
    simp only [itoWordStep, itoWordIntegral_cons_long, hu, hj, ↓reduceIte, ↓reduceDIte]
    exact lebIntegral_process_eq_integral (T := t) hu hut (hω J)
  apply contVersion_eq_of_tendsto
  have hF : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, X s ω) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval
      (by rw [uIcc_of_le ht]; exact (hω J).integrableOn_Icc)
  have hmem : t ∈ uIcc 0 t := by rw [uIcc_of_le ht]; exact ⟨ht, le_rfl⟩
  have hd : Tendsto (fun n => dyadicFloor n t) atTop (𝓝[uIcc 0 t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicFloor ht, Eventually.of_forall fun n => by
      rw [uIcc_of_le ht]; exact ⟨dyadicFloor_nonneg n t, dyadicFloor_le ht n⟩⟩
  refine ((hF t hmem).tendsto.comp hd).congr fun n => ?_
  exact (hstep _ (dyadicFloor_nonneg n t) (dyadicFloor_le ht n)).symm

/-- Integral of a finite weighted combination of continuous paths. -/
lemma integral_list_sum {t : ℝ} (ht : 0 ≤ t) {f : Word (d + 1) → ℝ → ℝ}
    (hf : ∀ w, ContinuousOn (f w) (Icc 0 t)) (L : List (ℝ × Word (d + 1))) :
    ContinuousOn (fun s => (L.map (fun p => p.1 * f p.2 s)).sum) (Icc 0 t) ∧
      ∫ s in (0 : ℝ)..t, (L.map (fun p => p.1 * f p.2 s)).sum =
        (L.map (fun p => p.1 * ∫ s in (0 : ℝ)..t, f p.2 s)).sum := by
  induction L with
  | nil => simp [continuousOn_const]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hc : ContinuousOn (fun s => p.1 * f p.2 s) (Icc 0 t) := continuousOn_const.mul (hf _)
    refine ⟨hc.add ih.1, ?_⟩
    have hi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 t) → IntervalIntegrable g volume 0 t :=
      fun hg => (by rw [uIcc_of_le ht]; exact hg : ContinuousOn _ (uIcc 0 t)).intervalIntegrable
    rw [intervalIntegral.integral_add (hi hc) (hi ih.1), intervalIntegral.integral_const_mul,
      ih.2]

lemma measurable_trapezoidSum_paperSig2 (B : MultiBrownian Ω P d) (I : Word (d + 1))
    (j : Fin (d + 1)) (t : ℝ) (n : ℕ) :
    Measurable (trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n) := by
  have hX : ∀ u, Measurable (fun ω => augCoord (MultiBrownian.W B) u ω j) := by
    intro u
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [augCoord, Fin.cases_zero]; exact measurable_const
    · simp only [augCoord, Fin.cases_succ]; exact MultiBrownian.W_meas B u i
  unfold trapezoidSum
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_const.mul ((measurable_paperSig2_coeff B 0 _ I).add
    (measurable_paperSig2_coeff B 0 _ I))).mul ((hX _).sub (hX _))

/-- **Dynamics, time letter.** -/
theorem paperSig2_dynamics_time (B : MultiBrownian Ω P d) (I : Word (d + 1)) {t : ℝ}
    (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) 0 t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [0])) := by
  refine tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_trapezoidSum_paperSig2 B I 0 t n).aestronglyMeasurable) ?_
  filter_upwards [ae_continuousOn_itoWordIntegral B ht, ae_itoWordIntegral_time_cons B ht]
    with ω hω h0
  set K := I.reverse
  have hH : ∀ s, (paperSig2 B 0 s ω).coeff I =
      ((contractions K).map (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := fun s => by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
  have hT : (paperSig2 B 0 t ω).coeff (I ++ [0]) =
      ((contractions K).map (fun p => p.1 * ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω p.2)).sum := by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      contractions_cons_zero, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp [h0]
  have hint := integral_list_sum (f := fun w s => itoWordIntegral B 0 s ω w) ht hω (contractions K)
  rw [hT, ← hint.2]
  have hc : ContinuousOn (fun s => (paperSig2 B 0 s ω).coeff I) (Icc 0 t) := by
    simpa only [hH] using hint.1
  have := tendsto_trapezoid_time ht hc
  simp only [hH] at this
  refine this.congr fun n => ?_
  simp only [trapezoidSum, augCoord, Fin.cases_zero, hH]

/-! ## Convergence in probability: algebra and moment criteria -/

section InMeasure

variable {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_add' (hf : TendstoInMeasure P f atTop F)
    (hg : TendstoInMeasure P g atTop G) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop (fun ω => F ω + G ω) := by
  intro ε hε
  have h2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hsum := (hf (ε / 2) h2).add (hg (ε / 2) h2)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le)
    (fun n => (measure_mono ?_).trans (measure_union_le _ _))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hc
  push Not at hc
  have h1 := edist_add_add_le (f n ω) (g n ω) (F ω) (G ω)
  have h3 : edist (f n ω) (F ω) + edist (g n ω) (G ω) < ε := by
    calc _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hc.1 hc.2
      _ = ε := ENNReal.add_halves ε
  exact absurd (hω.trans h1) (not_le.mpr h3)

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_const_mul (c : ℝ) (hf : TendstoInMeasure P f atTop F) :
    TendstoInMeasure P (fun n ω => c * f n ω) atTop (fun ω => c * F ω) := by
  intro ε hε
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, edist_self, nonpos_iff_eq_zero, hε.ne', Set.ofPred_false, measure_empty]
    exact tendsto_const_nhds
  have hc' : (0 : ENNReal) < ENNReal.ofReal |c| := ENNReal.ofReal_pos.2 (abs_pos.2 hc)
  have hcT : ENNReal.ofReal |c| ≠ ⊤ := ENNReal.ofReal_ne_top
  have h := hf (ε / ENNReal.ofReal |c|) (ENNReal.div_pos hε.ne' hcT)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
    (fun n => measure_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [edist_dist, Real.dist_eq, ← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ← Real.dist_eq, ← edist_dist] at hx
  rw [ENNReal.div_le_iff_le_mul (Or.inl hc'.ne') (Or.inl hcT), mul_comm]
  exact hx

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_congr_left (h : ∀ n ω, f n ω = g n ω)
    (hf : TendstoInMeasure P f atTop F) : TendstoInMeasure P g atTop F := by
  have : f = g := funext fun n => funext fun ω => h n ω
  rwa [← this]

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_congr_right (h : F =ᵐ[P] G) (hf : TendstoInMeasure P f atTop F) :
    TendstoInMeasure P f atTop G := by
  intro ε hε
  refine (hf ε hε).congr fun n => measure_congr ?_
  filter_upwards [h] with ω hω
  simp [hω]

omit [IsProbabilityMeasure P] in
/-- `L¹` control gives convergence in probability. -/
lemma tendstoInMeasure_of_integral_abs_le (hi : ∀ n, Integrable (fun ω => f n ω - F ω) P)
    {b : ℕ → ℝ} (hb : ∀ n, ∫ ω, |f n ω - F ω| ∂P ≤ b n) (hb0 : Tendsto b atTop (𝓝 0)) :
    TendstoInMeasure P f atTop F := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
  have hb' : Tendsto (fun n => ENNReal.ofReal (b n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hb0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb' (fun n => bot_le)
    (fun n => ?_)
  have hfn : f n - F = fun ω => f n ω - F ω := rfl
  rw [hfn, eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable]
  have e : ∫⁻ ω, ‖f n ω - F ω‖ₑ ∂P = ENNReal.ofReal (∫ ω, |f n ω - F ω| ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi n).abs (ae_of_all _ fun ω => abs_nonneg _)]
    congr 1; funext ω; simp [Real.enorm_eq_ofReal_abs]
  rw [e]
  exact ENNReal.ofReal_le_ofReal (hb n)

/-- `L²` control (to `0`) gives convergence in probability. -/
lemma tendstoInMeasure_zero_of_integral_sq_le (hL : ∀ n, MemLp (f n) 2 P)
    {b : ℕ → ℝ} (hb : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ b n) (hb0 : Tendsto b atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_integral_abs_le (fun n => by simpa using (hL n).integrable one_le_two)
    (b := fun n => Real.sqrt (max (b n) 0)) (fun n => ?_) ?_
  · have h := abs_integral_mul_le_sqrt (f := fun ω => |f n ω|) (g := fun _ => (1 : ℝ))
      (hL n).abs (memLp_const (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul,
      Real.sqrt_one] at h
    rw [abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)] at h
    simp only [sub_zero]
    exact h.trans (Real.sqrt_le_sqrt ((hb n).trans (le_max_left _ _)))
  · have h1 : Tendsto (fun n => max (b n) 0) atTop (𝓝 0) := by
      simpa using hb0.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using h1.sqrt

omit [IsProbabilityMeasure P] in
/-- A finite weighted sum of sequences converging in probability. -/
lemma tendstoInMeasure_list_sum {α : Type*} (L : List (ℝ × α)) {X : α → ℕ → Ω → ℝ}
    {Y : α → Ω → ℝ} (hX : ∀ p ∈ L, TendstoInMeasure P (X p.2) atTop (Y p.2)) :
    TendstoInMeasure P (fun n ω => (L.map (fun p => p.1 * X p.2 n ω)).sum) atTop
      (fun ω => (L.map (fun p => p.1 * Y p.2 ω)).sum) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    intro ε hε; simp [hε.ne']
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact tendstoInMeasure_add' (tendstoInMeasure_const_mul p.1 (hX p List.mem_cons_self))
      (ih fun q hq => hX q (List.mem_cons_of_mem _ hq))

end InMeasure

/-! ## Space letter: left sums and cross sums -/

/-- Uniform grid point `i t / (n + 1)`. -/
def dynGrid (t : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * t / (n + 1)

lemma dynGrid_succ_sub (t : ℝ) (n i : ℕ) : dynGrid t n (i + 1) - dynGrid t n i = t / (n + 1) := by
  simp only [dynGrid]; push_cast; ring

lemma dynGrid_nonneg {t : ℝ} (ht : 0 ≤ t) (n i : ℕ) : 0 ≤ dynGrid t n i := by
  unfold dynGrid; positivity

lemma dynGrid_le {t : ℝ} (ht : 0 ≤ t) {n i : ℕ} (hi : i ≤ n + 1) : dynGrid t n i ≤ t := by
  unfold dynGrid
  rw [div_le_iff₀ (by positivity)]
  have : (i : ℝ) ≤ n + 1 := by exact_mod_cast hi
  nlinarith

lemma dynGrid_mono {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : Monotone (dynGrid t n) := by
  intro i j hij
  unfold dynGrid
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  gcongr

/-- Left (Itô) Riemann sum of `Y` against `W^k` on the uniform grid. -/
def leftSum (B : MultiBrownian Ω P d) (k : Fin d) (Y : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), Y (dynGrid t n i) ω *
    wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω

/-- Discrete covariation sum `Σ ΔY ΔW^k` on the uniform grid. -/
def crossSum (B : MultiBrownian Ω P d) (k : Fin d) (Y : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ℝ :=
  ∑ i ∈ Finset.range (n + 1), (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω) *
    wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω

/-- Trapezoid sum = left sum + ½ covariation sum. -/
lemma trapezoidSum_succ_eq (B : MultiBrownian Ω P d) (k : Fin d) (Y : ℝ → Ω → ℝ) (t : ℝ)
    (n : ℕ) (ω : Ω) :
    trapezoidSum (MultiBrownian.W B) Y k.succ t n ω =
      leftSum B k Y t n ω + (1 / 2 : ℝ) * crossSum B k Y t n ω := by
  simp only [trapezoidSum, leftSum, crossSum, augCoord, Fin.cases_succ, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ((i : ℝ) + 1) * t / (n + 1) = dynGrid t n (i + 1) := by simp [dynGrid]
  have e2 : (i : ℝ) * t / (n + 1) = dynGrid t n i := rfl
  rw [e1, e2]
  change _ = Y (dynGrid t n i) ω * (MultiBrownian.W B (dynGrid t n (i + 1)) ω k -
      MultiBrownian.W B (dynGrid t n i) ω k) + 1 / 2 * ((Y (dynGrid t n (i + 1)) ω -
      Y (dynGrid t n i) ω) * (MultiBrownian.W B (dynGrid t n (i + 1)) ω k -
      MultiBrownian.W B (dynGrid t n i) ω k))
  ring

lemma leftSum_eq_unifRiemann (B : MultiBrownian Ω P d) (k : Fin d) (Y : ℝ → Ω → ℝ) (t : ℝ)
    (n : ℕ) (ω : Ω) : leftSum B k Y t n ω = unifRiemann B k Y t (n + 1) ω := by
  unfold leftSum unifRiemann
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : dynGrid t n i = (i : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) := by
    simp only [dynGrid]; push_cast; ring
  have e2 : dynGrid t n (i + 1) = ((i + 1 : ℕ) : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) := by
    simp only [dynGrid]; push_cast; ring
  rw [e1, e2]

lemma sum_wnnIncr_grid (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range (n + 1), wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω =
      MultiBrownian.W B t ω k - MultiBrownian.W B 0 ω k := by
  have h := Finset.sum_range_sub (fun i => MultiBrownian.W B (dynGrid t n i) ω k) (n + 1)
  have hN : dynGrid t n (n + 1) = t := by
    simp only [dynGrid]; push_cast; field_simp
  have h0 : dynGrid t n 0 = 0 := by simp [dynGrid]
  rw [hN, h0] at h
  exact h

/-- **Left sums converge to the next Itô letter.** -/
theorem ae_tendsto_leftSum (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => leftSum B k (fun s ω' => itoWordIntegral B 0 s ω' w) t n ω)
      atTop (𝓝 (itoWordIntegral B 0 t ω (k.succ :: w))) := by
  by_cases hw : w = []
  · subst hw
    refine Eventually.of_forall fun ω => ?_
    have e : ∀ n, leftSum B k (fun s ω' => itoWordIntegral B 0 s ω' []) t n ω =
        itoWordIntegral B 0 t ω [k.succ] := by
      intro n
      simp only [leftSum, itoWordIntegral_empty, one_mul, itoWordIntegral_space]
      exact sum_wnnIncr_grid B k n ω
    simp only [e]
    exact tendsto_const_nhds
  · obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B ht w hw).holderAdaptedEven le_rfl
    have hHA := hH.toHolderAdapted le_rfl
    filter_upwards [(itoIntegral_process_of_holderAdapted B k hHA ht).1,
      ae_itoWordIntegral_space_cons B ht k hw ht le_rfl] with ω h1 h2
    rw [h2]
    simp only [leftSum_eq_unifRiemann]
    exact h1

/-- Pathwise: a Lipschitz path has vanishing covariation with a continuous path. -/
theorem tendsto_crossSum_lipschitz {t : ℝ} (ht : 0 ≤ t) {y x : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hy : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → |y b - y a| ≤ M * (b - a))
    (hx : ContinuousOn x (Icc 0 t)) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      (y (dynGrid t n (i + 1)) - y (dynGrid t n i)) * (x (dynGrid t n (i + 1)) - x (dynGrid t n i)))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hx
  rw [Metric.uniformContinuousOn_iff_le] at huc
  set ε' := ε / (2 * (M * t + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδx⟩ := huc ε' hε'0
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hh : t / (n + 1) ≤ δ := by
    rw [div_le_iff₀ hn1]
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 := (div_lt_iff₀ hδ).1 hN
    nlinarith
  rw [Real.dist_eq, sub_zero]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      |(y (dynGrid t n (i + 1)) - y (dynGrid t n i)) * (x (dynGrid t n (i + 1)) - x (dynGrid t n i))|
        ≤ M * (t / (n + 1)) * ε' := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have ha0 := dynGrid_nonneg ht n i
    have hab := dynGrid_mono ht n (Nat.le_succ i)
    have hbt := dynGrid_le ht (n := n) (i := i + 1) (by omega)
    rw [abs_mul]
    have h1 := hy _ _ ha0 hab hbt
    rw [dynGrid_succ_sub] at h1
    have h2 : |x (dynGrid t n (i + 1)) - x (dynGrid t n i)| ≤ ε' := by
      have := hδx (dynGrid t n (i + 1)) ⟨ha0.trans hab, hbt⟩ (dynGrid t n i) ⟨ha0, hab.trans hbt⟩
        (by rw [Real.dist_eq, dynGrid_succ_sub, abs_of_nonneg (by positivity)]; exact hh)
      rwa [Real.dist_eq] at this
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), |(y (dynGrid t n (i + 1)) - y (dynGrid t n i)) *
        (x (dynGrid t n (i + 1)) - x (dynGrid t n i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), M * (t / (n + 1)) * ε' := Finset.sum_le_sum hterm
    _ = M * t * ε' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
    _ < ε := by
        have h3 : M * t < 2 * (M * t + 1) := by nlinarith [mul_nonneg hM ht]
        calc M * t * ε' = ε * (M * t / (2 * (M * t + 1))) := by rw [hε']; ring
          _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 h3) hε
          _ = ε := mul_one ε

lemma continuous_W_coord (B : MultiBrownian Ω P d) (k : Fin d) (ω : Ω) :
    Continuous fun s : ℝ => MultiBrownian.W B s ω k :=
  (B.pathContinuous k ω).comp continuous_real_toNNReal

/-- **Time-headed words have vanishing covariation with `W^k`** (pathwise, a.s.). -/
theorem ae_tendsto_crossSum_time (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => crossSum B k
      (fun s ω' => itoWordIntegral B 0 s ω' ((0 : Fin (d + 1)) :: w)) t n ω) atTop (𝓝 0) := by
  have hgrid : ∀ᵐ ω ∂P, ∀ n i : ℕ, itoWordIntegral B 0 (dynGrid t n i) ω ((0 : Fin (d + 1)) :: w)
      = ∫ s in (0 : ℝ)..dynGrid t n i, itoWordIntegral B 0 s ω w := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro i
    filter_upwards [ae_itoWordIntegral_time_cons B (dynGrid_nonneg ht n i)] with ω hω
    exact hω w
  filter_upwards [ae_continuousOn_itoWordIntegral B ht, hgrid] with ω hω hg
  set g := fun s => itoWordIntegral B 0 s ω w
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hω w)
  set M' := max M 0
  have hint : ∀ b, 0 ≤ b → b ≤ t → IntervalIntegrable g volume 0 b := fun b hb hbt =>
    ((hω w).mono (Icc_subset_Icc le_rfl hbt)).intervalIntegrable_of_Icc hb
  have hy : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      |(∫ s in (0 : ℝ)..b, g s) - ∫ s in (0 : ℝ)..a, g s| ≤ M' * (b - a) := by
    intro a b ha hab hbt
    rw [intervalIntegral.integral_interval_sub_left (hint b (ha.trans hab) hbt)
      (hint a ha (hab.trans hbt))]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := g)
      (C := M') (fun s hs => by
        rw [uIoc_of_le hab] at hs
        exact (hM s ⟨ha.trans hs.1.le, hs.2.trans hbt⟩).trans (le_max_left _ _))
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
  have h := tendsto_crossSum_lipschitz ht (le_max_right M 0) hy
    (continuous_W_coord B k ω).continuousOn
  refine h.congr fun n => ?_
  simp only [crossSum, hg]
  rfl

lemma tendsto_div_succ (c : ℝ) : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
  simpa [div_eq_mul_inv] using this

lemma integral_sq_le_sqrt_four {f : Ω → ℝ} (hm : AEStronglyMeasurable f P)
    (h4 : Integrable (fun ω => f ω ^ 4) P) :
    ∫ ω, f ω ^ 2 ∂P ≤ Real.sqrt (∫ ω, f ω ^ 4 ∂P) := by
  have hL : MemLp (fun ω => f ω ^ 2) 2 P :=
    memLp_two_of_integrable_sq (hm.pow 2) (by simpa [← pow_mul] using h4)
  have h := abs_integral_mul_le_sqrt hL (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul, Real.sqrt_one,
    ← pow_mul] at h
  exact (le_abs_self _).trans h

/-- Uniform second moments of Itô word integrals on `[0, t]`. -/
lemma exists_integral_sq_itoWordIntegral_le (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) : ∃ C, 0 ≤ C ∧ ∀ s, 0 ≤ s → s ≤ t →
      ∫ ω, itoWordIntegral B 0 s ω w ^ 2 ∂P ≤ C := by
  by_cases hw : w = []
  · subst hw
    exact ⟨1, zero_le_one, fun s _ _ => by simp [itoWordIntegral_empty]⟩
  · have hX := levelBound_itoWordIntegral B ht w hw
    refine ⟨max (wordConst 2 w * t ^ wordExp w) 0, le_max_right _ _, fun s hs hst => ?_⟩
    have h4 := integrable_pow_of_memLp_four (k := 4)
      (by simpa using memLp_itoWordIntegral B hs w (le_refl 2)) le_rfl
    refine (integral_sq_le_sqrt_four (measurable_itoWordIntegral B 0 s w).aestronglyMeasurable
      h4).trans (le_trans ?_ (le_max_left _ _))
    have := hX.mom_le_T (le_refl 2) s hs hst
    simpa [nrm, Real.sqrt_eq_rpow] using this

/-- **Frozen remainders** with fourth moments `O(h⁴)` sum to `0` against `ΔW^k`. -/
theorem tendstoInMeasure_frozenSum (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    {R : ℕ → ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (hRm : ∀ n i, AEStronglyMeasurable (R n i) P)
    (hR4 : ∀ n i, i < n + 1 → Integrable (fun ω => R n i ω ^ 4) P ∧
      ∫ ω, R n i ω ^ 4 ∂P ≤ C * (t / (n + 1)) ^ 4) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ Finset.range (n + 1),
      R n i ω * wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω) atTop (fun _ => 0) := by
  set c := Real.sqrt (Real.sqrt C)
  have hterm : ∀ n i, i < n + 1 →
      Integrable (fun ω => R n i ω * wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω) P ∧
      ∫ ω, |R n i ω * wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω| ∂P ≤
        c * (t / (n + 1)) * Real.sqrt (t / (n + 1)) := by
    intro n i hi
    obtain ⟨h4, hb⟩ := hR4 n i hi
    have ha := dynGrid_nonneg ht n i
    have hab := dynGrid_mono ht n (Nat.le_succ i)
    have hh0 : 0 ≤ t / (n + 1) := by positivity
    have h2 : Integrable (fun ω => R n i ω ^ 2) P := by
      refine Integrable.mono' (g := fun ω => (R n i ω ^ 4 + 1) / 2)
        ((h4.add (integrable_const (1 : ℝ))).div_const 2) ((hRm n i).pow 2)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (R n i ω ^ 2 - 1)]
    have hRL : MemLp (R n i) 2 P := memLp_two_of_integrable_sq (hRm n i) h2
    have hΔL : MemLp (wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1))) 2 P :=
      memLp_two_of_integrable_sq (measurable_wnnIncr B k _ _).aestronglyMeasurable
        (by simpa using integrable_wnnIncr_pow_even B k 1 ha hab)
    refine ⟨integrable_mul_of_memLp_two hRL hΔL, ?_⟩
    have hcs := abs_integral_mul_le_sqrt hRL.norm hΔL.norm
    simp only [Real.norm_eq_abs, sq_abs] at hcs
    rw [integral_wnnIncr_sq B k ha hab, dynGrid_succ_sub] at hcs
    simp_rw [abs_mul]
    refine (le_abs_self _).trans (hcs.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have e : Real.sqrt (Real.sqrt (C * (t / (n + 1)) ^ 4)) = c * (t / (n + 1)) := by
      rw [show (t / (n + 1)) ^ 4 = ((t / (n + 1)) ^ 2) ^ 2 by ring, Real.sqrt_mul hC,
        Real.sqrt_sq (sq_nonneg _), Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_sq hh0]
    rw [← e]
    exact Real.sqrt_le_sqrt ((integral_sq_le_sqrt_four (hRm n i) h4).trans
      (Real.sqrt_le_sqrt hb))
  refine tendstoInMeasure_of_integral_abs_le (F := fun _ => 0)
    (b := fun n => c * t * Real.sqrt (t / (n + 1))) (fun n => ?_) (fun n => ?_) ?_
  · simpa using integrable_finsetSum _ fun i hi => (hterm n i (Finset.mem_range.1 hi)).1
  · simp only [sub_zero]
    calc _ ≤ ∫ ω, ∑ i ∈ Finset.range (n + 1),
          |R n i ω * wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω| ∂P :=
          integral_mono (integrable_finsetSum _ fun i hi =>
              (hterm n i (Finset.mem_range.1 hi)).1).abs
            (integrable_finsetSum _ fun i hi => (hterm n i (Finset.mem_range.1 hi)).1.abs)
            fun ω => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (n + 1),
          ∫ ω, |R n i ω * wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω| ∂P :=
          integral_finsetSum _ fun i hi => (hterm n i (Finset.mem_range.1 hi)).1.abs
      _ ≤ ∑ _i ∈ Finset.range (n + 1), c * (t / (n + 1)) * Real.sqrt (t / (n + 1)) :=
          Finset.sum_le_sum fun i hi => (hterm n i (Finset.mem_range.1 hi)).2
      _ = c * t * Real.sqrt (t / (n + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  · have := ((tendsto_div_succ t).sqrt).const_mul (c * t)
    simpa using this

/-- **Martingale part** `Σ g_i (ΔW^{k'} ΔW^k − δ h) → 0` in probability. -/
theorem tendstoInMeasure_cellSum (B : MultiBrownian Ω P d) (k' k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ Finset.range (n + 1),
      itoWordIntegral B 0 (dynGrid t n i) ω w *
        cellProd B k' k (dynGrid t n i) (dynGrid t n (i + 1)) ω) atTop (fun _ => 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_itoWordIntegral_le B ht w
  have hL : ∀ n i, MemLp (fun ω => itoWordIntegral B 0 (dynGrid t n i) ω w) 2 P := fun n i =>
    (memLp_itoWordIntegral B (dynGrid_nonneg ht n i) w (le_refl 2)).mono_exponent (by norm_num)
  have hsq := fun n => integral_sum_mul_cellProd_sq B k' k (τ := dynGrid t n)
    (dynGrid_nonneg ht n 0) (dynGrid_mono ht n)
    (fun i ω => itoWordIntegral B 0 (dynGrid t n i) ω w) (n + 1)
    (fun i _ => measurable_itoWordIntegral_pathFiltration B le_rfl (dynGrid_nonneg ht n i) le_rfl w)
    (fun i _ => hL n i)
  have hg0 := gaussMoment_nonneg 2
  refine tendstoInMeasure_zero_of_integral_sq_le (fun n => ?_)
    (b := fun n => C * (gaussMoment 2 + 1) * t ^ 2 / (n + 1)) (fun n => ?_) ?_
  · refine memLp_two_of_integrable_sq ?_ (hsq n).1
    exact (Finset.measurable_sum _ fun i _ => (measurable_itoWordIntegral B 0 _ w).mul
      (measurable_cellProd B k' k _ _)).aestronglyMeasurable
  · rw [(hsq n).2]
    calc _ ≤ ∑ _i ∈ Finset.range (n + 1), C * ((gaussMoment 2 + 1) * (t / (n + 1)) ^ 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have ha := dynGrid_nonneg ht n i
          have hab := dynGrid_mono ht n (Nat.le_succ i)
          refine mul_le_mul (hC _ ha (dynGrid_le ht (by omega))) ?_
            (integral_nonneg fun ω => sq_nonneg _) hC0
          rw [← dynGrid_succ_sub t n i]
          exact (integrable_cellProd_sq_and_le B k' k ha hab).2
      _ = C * (gaussMoment 2 + 1) * t ^ 2 / (n + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  · exact tendsto_div_succ _

/-- **Bracket part**: left Riemann sums of `G_w` against `dt`. -/
theorem tendstoInMeasure_lebSum (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ Finset.range (n + 1),
      itoWordIntegral B 0 (dynGrid t n i) ω w * (dynGrid t n (i + 1) - dynGrid t n i)) atTop
      (fun ω => ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω w) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => (Finset.measurable_sum _ fun i _ =>
    (measurable_itoWordIntegral B 0 _ w).mul_const _).aestronglyMeasurable) ?_
  filter_upwards [ae_continuousOn_itoWordIntegral B ht] with ω hω
  refine (tendsto_lebRiemann_of_continuousOn ht (hω w)).congr fun n =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [dynGrid_succ_sub]
  simp only [dynGrid, mul_div_assoc]

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_zero_seq :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) := by
  intro ε hε
  simp [hε.ne']

lemma wnnIncr_eq_W (B : MultiBrownian Ω P d) (k : Fin d) (a b : ℝ) (ω : Ω) :
    wnnIncr B k a b ω = MultiBrownian.W B b ω k - MultiBrownian.W B a ω k := rfl

lemma measurable_crossSum_ito (B : MultiBrownian Ω P d) (k : Fin d) (w : Word (d + 1)) (t : ℝ)
    (n : ℕ) : Measurable (crossSum B k (fun s ω => itoWordIntegral B 0 s ω w) t n) :=
  Finset.measurable_sum _ fun _ _ => ((measurable_itoWordIntegral B 0 _ w).sub
    (measurable_itoWordIntegral B 0 _ w)).mul (measurable_wnnIncr B k _ _)

lemma measurable_leftSum_ito (B : MultiBrownian Ω P d) (k : Fin d) (w : Word (d + 1)) (t : ℝ)
    (n : ℕ) : Measurable (leftSum B k (fun s ω => itoWordIntegral B 0 s ω w) t n) :=
  Finset.measurable_sum _ fun _ _ => (measurable_itoWordIntegral B 0 _ w).mul
    (measurable_wnnIncr B k _ _)

/-- Frozen / martingale / bracket decomposition of the covariation sum. -/
lemma crossSum_eq_decomp (B : MultiBrownian Ω P d) (k k' : Fin d) (Y g : ℝ → Ω → ℝ) (t : ℝ)
    (n : ℕ) (ω : Ω) :
    ((∑ i ∈ Finset.range (n + 1), (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
        g (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) *
        wnnIncr B k (dynGrid t n i) (dynGrid t n (i + 1)) ω) +
      ∑ i ∈ Finset.range (n + 1), g (dynGrid t n i) ω *
        cellProd B k' k (dynGrid t n i) (dynGrid t n (i + 1)) ω) +
      (if k' = k then ∑ i ∈ Finset.range (n + 1),
        g (dynGrid t n i) ω * (dynGrid t n (i + 1) - dynGrid t n i) else 0) =
    crossSum B k Y t n ω := by
  unfold crossSum cellProd
  by_cases h : k' = k
  · subst h
    simp only [eq_self, ite_true, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [h, ite_false, sub_zero, add_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Fourth-moment frozen bound for an Itô integral version. -/
lemma exists_frozen_bound (B : MultiBrownian Ω P d) (k' : Fin d) {t : ℝ} {H : ℝ → Ω → ℝ} {K : ℝ}
    (hHA : HolderAdapted B H t K) (ht : 0 ≤ t) {Y : ℝ → Ω → ℝ}
    (hY : ∀ u, 0 ≤ u → u ≤ t → (fun ω => Y u ω) =ᵐ[P]
      fun ω => itoIntegral_process B k' H 0 u ω) :
    ∃ C, 0 ≤ C ∧ ∀ n i, i < n + 1 →
      Integrable (fun ω => (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
        H (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4) P ∧
      ∫ ω, (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
        H (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4 ∂P ≤
        C * (t / (n + 1)) ^ 4 := by
  refine ⟨128 * gaussFourthConst * K, by
    have := gaussFourthConst_nonneg; have := hHA.K_nonneg; positivity, fun n i hi => ?_⟩
  have ha := dynGrid_nonneg ht n i
  have hab := dynGrid_mono ht n (Nat.le_succ i)
  have hbt := dynGrid_le ht (n := n) (i := i + 1) (by omega)
  have hf := integral_itoIntegral_process_sub_frozen_pow_four_le B k' hHA ha hab hbt
  have hae : (fun ω => (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
      H (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4) =ᵐ[P]
      fun ω => (itoIntegral_process B k' H 0 (dynGrid t n (i + 1)) ω -
        itoIntegral_process B k' H 0 (dynGrid t n i) ω -
        H (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4 := by
    filter_upwards [hY _ (ha.trans hab) hbt, hY _ ha (hab.trans hbt)] with ω h1 h2
    rw [h1, h2]
  refine ⟨hf.1.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, ← dynGrid_succ_sub t n i]
  exact hf.2

/-- **Space-headed words**: `Σ ΔI^{k' w} ΔW^k → δ_{k'k} ∫ I^w`. -/
theorem tendstoInMeasure_crossSum_space (B : MultiBrownian Ω P d) (k k' : Fin d) {t : ℝ}
    (ht : 0 ≤ t) (w : Word (d + 1)) :
    TendstoInMeasure P (fun n => crossSum B k
      (fun s ω => itoWordIntegral B 0 s ω (k'.succ :: w)) t n) atTop
      (fun ω => if k' = k then ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω w else 0) := by
  set Y : ℝ → Ω → ℝ := fun s ω => itoWordIntegral B 0 s ω (k'.succ :: w)
  set g : ℝ → Ω → ℝ := fun s ω => itoWordIntegral B 0 s ω w
  obtain ⟨C, hC, hR4⟩ : ∃ C, 0 ≤ C ∧ ∀ n i, i < n + 1 →
      Integrable (fun ω => (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
        g (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4) P ∧
      ∫ ω, (Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
        g (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω) ^ 4 ∂P ≤
        C * (t / (n + 1)) ^ 4 := by
    by_cases hw : w = []
    · subst hw
      refine ⟨0, le_rfl, fun n i _ => ?_⟩
      have h0 : ∀ ω, Y (dynGrid t n (i + 1)) ω - Y (dynGrid t n i) ω -
          g (dynGrid t n i) ω * wnnIncr B k' (dynGrid t n i) (dynGrid t n (i + 1)) ω = 0 := by
        intro ω
        simp only [Y, g, itoWordIntegral_space, itoWordIntegral_empty, one_mul, wnnIncr_eq_W]
        ring
      simp [h0]
    · obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B ht w hw).holderAdaptedEven le_rfl
      exact exists_frozen_bound B k' (hH.toHolderAdapted le_rfl) ht
        (fun u hu hut => ae_itoWordIntegral_space_cons B ht k' hw hu hut)
  have hA := tendstoInMeasure_frozenSum B k ht hC (fun n i =>
    (((measurable_itoWordIntegral B 0 _ _).sub (measurable_itoWordIntegral B 0 _ _)).sub
      ((measurable_itoWordIntegral B 0 _ w).mul (measurable_wnnIncr B k' _ _))).aestronglyMeasurable)
    hR4
  have hM := tendstoInMeasure_cellSum B k' k ht w
  have hL : TendstoInMeasure P (fun n ω => if k' = k then ∑ i ∈ Finset.range (n + 1),
      g (dynGrid t n i) ω * (dynGrid t n (i + 1) - dynGrid t n i) else 0) atTop
      (fun ω => if k' = k then ∫ s in (0 : ℝ)..t, g s ω else 0) := by
    by_cases h : k' = k
    · simp only [h, ite_true]; exact tendstoInMeasure_lebSum B ht w
    · simp only [h, ite_false]; exact tendstoInMeasure_zero_seq
  have hsum := tendstoInMeasure_add' (tendstoInMeasure_add' hA hM) hL
  refine tendstoInMeasure_congr_left (fun n ω => crossSum_eq_decomp B k k' Y g t n ω)
    (tendstoInMeasure_congr_right (Eventually.of_forall fun ω => ?_) hsum)
  simp only [zero_add]
  rfl

/-- Limit of the covariation sum of `I^w` against `W^k`. -/
def crossLimit (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) : Word (d + 1) → Ω → ℝ
  | [], _ => 0
  | l :: w, ω => if l = k.succ then ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω w else 0

@[simp] lemma crossLimit_nil (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) (ω : Ω) :
    crossLimit B k t [] ω = 0 := rfl

@[simp] lemma crossLimit_cons (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) (l : Fin (d + 1))
    (w : Word (d + 1)) (ω : Ω) : crossLimit B k t (l :: w) ω =
      if l = k.succ then ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω w else 0 := rfl

/-- **Covariation limits for every word.** -/
theorem tendstoInMeasure_crossSum (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (w : Word (d + 1)) :
    TendstoInMeasure P (fun n => crossSum B k (fun s ω => itoWordIntegral B 0 s ω w) t n) atTop
      (crossLimit B k t w) := by
  match w with
  | [] =>
    have e : (fun n => crossSum B k (fun s ω => itoWordIntegral B 0 s ω []) t n) =
        fun _ _ => 0 := by
      funext n ω; simp [crossSum, itoWordIntegral_empty]
    rw [e]
    exact tendstoInMeasure_zero_seq
  | l :: w =>
    refine Fin.cases ?_ (fun k' => ?_) l
    · have h0 : crossLimit B k t ((0 : Fin (d + 1)) :: w) = fun _ => 0 := by
        funext ω; simp [crossLimit_cons, (Fin.succ_ne_zero k).symm]
      rw [h0]
      exact tendstoInMeasure_of_tendsto_ae
        (fun n => (measurable_crossSum_ito B k _ t n).aestronglyMeasurable)
        (ae_tendsto_crossSum_time B k ht w)
    · have h1 : crossLimit B k t (k'.succ :: w) = fun ω =>
          if k' = k then ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω w else 0 := by
        funext ω; simp [crossLimit_cons, Fin.succ_inj]
      rw [h1]
      exact tendstoInMeasure_crossSum_space B k k' ht w

/-- **Per-word trapezoid limit.** -/
theorem tendstoInMeasure_trapezoid_word (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ}
    (ht : 0 ≤ t) (w : Word (d + 1)) :
    TendstoInMeasure P (fun n => trapezoidSum (MultiBrownian.W B)
      (fun s ω => itoWordIntegral B 0 s ω w) k.succ t n) atTop
      (fun ω => itoWordIntegral B 0 t ω (k.succ :: w) + (1 / 2 : ℝ) * crossLimit B k t w ω) := by
  have hleft : TendstoInMeasure P (fun n => leftSum B k (fun s ω => itoWordIntegral B 0 s ω w) t n)
      atTop (fun ω => itoWordIntegral B 0 t ω (k.succ :: w)) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => (measurable_leftSum_ito B k w t n).aestronglyMeasurable)
      (ae_tendsto_leftSum B k ht w)
  exact tendstoInMeasure_congr_left (fun n ω => (trapezoidSum_succ_eq B k _ t n ω).symm)
    (tendstoInMeasure_add' hleft
      (tendstoInMeasure_const_mul (1 / 2 : ℝ) (tendstoInMeasure_crossSum B k ht w)))

omit [MeasurableSpace Ω] in
lemma trapezoidSum_const_mul_add (X : ℝ → Ω → Fin d → ℝ) (Y Z : ℝ → Ω → ℝ) (c : ℝ)
    (j : Fin (d + 1)) (t : ℝ) (n : ℕ) (ω : Ω) :
    trapezoidSum X (fun s ω => c * Y s ω + Z s ω) j t n ω =
      c * trapezoidSum X Y j t n ω + trapezoidSum X Z j t n ω := by
  unfold trapezoidSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [MeasurableSpace Ω] in
lemma trapezoidSum_list_sum {α : Type*} (X : ℝ → Ω → Fin d → ℝ) (L : List (ℝ × α))
    (Y : α → ℝ → Ω → ℝ) (j : Fin (d + 1)) (t : ℝ) (n : ℕ) (ω : Ω) :
    trapezoidSum X (fun s ω => (L.map (fun p => p.1 * Y p.2 s ω)).sum) j t n ω =
      (L.map (fun p => p.1 * trapezoidSum X (Y p.2) j t n ω)).sum := by
  induction L with
  | nil => simp [trapezoidSum]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [trapezoidSum_const_mul_add, ih]

/-- Combinatorics of the covariation limits over contractions. -/
lemma sum_contractions_crossLimit (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) (ω : Ω)
    (K : Word (d + 1)) :
    ((contractions K).map (fun p => p.1 * crossLimit B k t p.2 ω)).sum =
      if K.head? = some k.succ then ((contractions K.tail).map
        (fun p => p.1 * ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω p.2)).sum else 0 := by
  match K with
  | [] => simp [contractions]
  | l :: K =>
    rw [contractions_cons]
    have h2 : ((if K.head? = some l ∧ (l : ℕ) ≠ 0 then (contractions K.tail).map
        (fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)) else []).map
        (fun p => p.1 * crossLimit B k t p.2 ω)).sum = 0 := by
      split_ifs
      · have h0k : (0 : Fin (d + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
        simp [Function.comp_def, h0k]
      · simp
    rw [List.map_append, List.sum_append, h2, add_zero, List.map_map]
    by_cases hl : l = k.succ
    · subst hl
      simp [crossLimit_cons, Function.comp_def]
    · simp [crossLimit_cons, Function.comp_def, hl]

/-! ## Space letter -/

/-- **Dynamics, space letter.** -/
theorem paperSig2_dynamics_space (B : MultiBrownian Ω P d) (I : Word (d + 1)) (j : Fin (d + 1))
    (hj : j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [j])) := by
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hj
  set K := I.reverse with hKdef
  have hH : ∀ s ω, (paperSig2 B 0 s ω).coeff I =
      ((contractions K).map (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := fun s ω => by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
  have h1 := tendstoInMeasure_list_sum (P := P) (contractions K)
    (X := fun w n ω => trapezoidSum (MultiBrownian.W B)
      (fun s ω => itoWordIntegral B 0 s ω w) k.succ t n ω)
    (Y := fun w ω => itoWordIntegral B 0 t ω (k.succ :: w) + (1 / 2 : ℝ) * crossLimit B k t w ω)
    (fun p _ => tendstoInMeasure_trapezoid_word B k ht p.2)
  refine tendstoInMeasure_congr_left (fun n ω => ?_) (tendstoInMeasure_congr_right ?_ h1)
  · simp only [hH]
    exact (trapezoidSum_list_sum (MultiBrownian.W B) (contractions K)
      (fun w s ω => itoWordIntegral B 0 s ω w) k.succ t n ω).symm
  · filter_upwards [ae_itoWordIntegral_time_cons B ht] with ω h0
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
    rw [← hKdef, contractions_cons]
    simp only [mul_add, List.sum_map_add, ← mul_assoc, List.map_append, List.sum_append,
      List.map_map]
    have hc := sum_contractions_crossLimit B k t ω K
    have e : ((contractions K).map (fun p => p.1 * (1 / 2 : ℝ) * crossLimit B k t p.2 ω)).sum =
        (1 / 2 : ℝ) * ((contractions K).map (fun p => p.1 * crossLimit B k t p.2 ω)).sum := by
      rw [← List.sum_map_mul_left]; congr 1; refine List.map_congr_left fun p _ => by ring
    rw [e, hc]
    congr 1
    · have hk : ((k.succ : Fin (d + 1)) : ℕ) ≠ 0 := by simp
      by_cases hK : K.head? = some k.succ
      · simp only [hK, hk, ne_eq, not_false_eq_true, and_true, ite_true]
        rw [List.map_map, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun p _ => ?_
        simp only [Function.comp_apply, ← h0]
        ring
      · simp [hK]

/-- **Signature dynamics** `dŴ = Ŵ ⊗ ∘dX` for the Brownian Stratonovich signature. -/
theorem paperSig2_dynamics (B : MultiBrownian Ω P d) (I : Word (d + 1)) (j : Fin (d + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [j])) := by
  by_cases hj : j = 0
  · subst hj; exact paperSig2_dynamics_time B I ht
  · exact paperSig2_dynamics_space B I j hj ht

end SignatureVolatility
