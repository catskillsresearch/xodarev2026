module

public import SignatureVolatility.ProlongedBrownianSetup.PaperSig

@[expose] public section


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

/-! ## Space letter -/

/-- **Dynamics, space letter.** -/
theorem paperSig2_dynamics_space (B : MultiBrownian Ω P d) (I : Word (d + 1)) (j : Fin (d + 1))
    (hj : j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [j])) := by
  sorry

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
