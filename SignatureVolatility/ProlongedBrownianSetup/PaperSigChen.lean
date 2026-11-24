module

public import SignatureVolatility.ProlongedBrownianSetup.ShiftedWordIntegral

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace SignatureVolatility

/-!
# Chen and shuffle identities for the paper signature `Ŵ`

Chen is proved first for the Itô word integrals, by induction on the word. The step uses the
restart identity of `ShiftedWordIntegral` and the additivity of the Itô integral in its upper
limit. It is then carried to the Stratonovich coordinates, because the contraction expansion
`stratWordIntegral_eq_list` is compatible with deconcatenation.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Deconcatenation sums -/

/-- `Σ_{K = A ++ C} G(A) H(C)` (split after the first `i` letters, `0 ≤ i ≤ |K|`). -/
def chenSum (G H : Word (d + 1) → ℝ) (K : Word (d + 1)) : ℝ :=
  ∑ i ∈ Finset.range (K.length + 1), G (K.take i) * H (K.drop i)

lemma chenSum_nil (G H : Word (d + 1) → ℝ) : chenSum G H [] = G [] * H [] := by
  simp [chenSum]

lemma chenSum_cons (G H : Word (d + 1) → ℝ) (j : Fin (d + 1)) (K : Word (d + 1)) :
    chenSum G H (j :: K) = G [] * H (j :: K) + chenSum (fun A => G (j :: A)) H K := by
  unfold chenSum
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero]
  ring

/-! ## Probability helpers -/

omit [IsProbabilityMeasure P] in
/-- Fixed-time a.s. equalities of a.s. continuous processes hold a.s. for all times. -/
lemma ae_forall_of_continuousOn {f g : ℝ → Ω → ℝ} {s : ℝ}
    (hf : ∀ᵐ ω ∂P, ∀ N : ℕ, ContinuousOn (fun t => f t ω) (Icc s N))
    (hg : ∀ᵐ ω ∂P, ∀ N : ℕ, ContinuousOn (fun t => g t ω) (Icc s N))
    (h : ∀ t, s < t → f t =ᵐ[P] g t) : ∀ᵐ ω ∂P, ∀ t, s ≤ t → f t ω = g t ω := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, s < q → f q ω = g q ω := by
    rw [ae_all_iff]; intro q
    by_cases hq : s < q
    · filter_upwards [h q hq] with ω hω _
      exact hω
    · exact ae_of_all _ fun ω h' => absurd h' hq
  filter_upwards [hf, hg, hq] with ω hf hg hq t ht
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hsN : s < N := ht.trans_lt hN
  have hEq : EqOn (fun t => f t ω) (fun t => g t ω) (Icc s N) := by
    refine EqOn.of_subset_closure (s := Ioo s N ∩ Set.range ((↑) : ℚ → ℝ)) ?_ (hf N) (hg N)
      (fun x hx => Ioo_subset_Icc_self hx.1) ?_
    · rintro x ⟨hx, q, rfl⟩
      exact hq q hx.1
    · calc Icc s (N : ℝ) = closure (Ioo s N) := (closure_Ioo hsN.ne).symm
        _ ⊆ closure (Ioo s N ∩ Set.range ((↑) : ℚ → ℝ)) :=
          closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
            isClosed_closure
  exact hEq ⟨ht, hN.le⟩

omit [IsProbabilityMeasure P] in
lemma ae_eq_of_tendstoInMeasure_of_ae_tendsto {f : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (h1 : TendstoInMeasure P f atTop F) (h2 : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (G ω))) :
    F =ᵐ[P] G := by
  obtain ⟨ns, hns, hlim⟩ := h1.exists_seq_tendsto_ae
  filter_upwards [hlim, h2] with ω h1 h2
  exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_sub' {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : TendstoInMeasure P f atTop F) (hg : TendstoInMeasure P g atTop G) :
    TendstoInMeasure P (fun n ω => f n ω - g n ω) atTop (fun ω => F ω - G ω) := by
  have h := tendstoInMeasure_add' hf (tendstoInMeasure_const_mul (-1) hg)
  refine tendstoInMeasure_congr_left (fun n ω => by ring)
    (tendstoInMeasure_congr_right (Eventually.of_forall fun ω => by simp only; ring) h)

lemma integrable_sq_of_integrable_pow_four {f : Ω → ℝ} (hm : AEStronglyMeasurable f P)
    (h4 : Integrable (fun ω => f ω ^ 4) P) : Integrable (fun ω => f ω ^ 2) P := by
  refine Integrable.mono' (g := fun ω => (f ω ^ 4 + 1) / 2)
    ((h4.add (integrable_const (1 : ℝ))).div_const 2) (hm.pow 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f ω ^ 2 - 1)]

/-! ## Restarted word integrals: continuity, Riemann sums, time integrals -/

/-- A.s., every `s`-start Itô word coordinate is continuous on every `[s, N]`. -/
lemma ae_continuousOn_itoWordIntegral_start (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ A : Word (d + 1),
      ContinuousOn (fun r => itoWordIntegral B s r ω A) (Icc s N) := by
  have hsh : ∀ᵐ ω ∂P, ∀ A : Word (d + 1), ∀ r, s ≤ r →
      itoWordIntegral B s r ω A = itoWordIntegral (B.shift s.toNNReal) 0 (r - s) ω A :=
    ae_all_iff.2 fun A => ae_itoWordIntegral_shift B hs A
  have hc : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ J : Word (d + 1),
      ContinuousOn (fun x => itoWordIntegral (B.shift s.toNNReal) 0 x ω J) (Icc 0 N) :=
    ae_all_iff.2 fun N => ae_continuousOn_itoWordIntegral _ (Nat.cast_nonneg N)
  filter_upwards [hsh, hc] with ω hsh hc N A
  have hmaps : MapsTo (fun r : ℝ => r - s) (Icc s (N : ℝ)) (Icc 0 (N : ℝ)) := fun r hr =>
    ⟨sub_nonneg.2 hr.1, by linarith [hr.2]⟩
  have hcomp : ContinuousOn (fun r => itoWordIntegral (B.shift s.toNNReal) 0 (r - s) ω A)
      (Icc s (N : ℝ)) :=
    (hc N A).comp (continuousOn_id.sub continuousOn_const) hmaps
  exact hcomp.congr fun r hr => hsh A r hr.1

lemma itoRiemann_process_shift (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s) (k : Fin d)
    {H H' : ℝ → Ω → ℝ} {ω : Ω} (hH : ∀ r, s ≤ r → H r ω = H' (r - s) ω) {t : ℝ} (hst : s ≤ t)
    (n : ℕ) :
    itoRiemann_process B k H s t n ω =
      itoRiemann_process (B.shift s.toNNReal) k H' 0 (t - s) n ω := by
  simp only [itoRiemann_process, sub_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 := sub_nonneg.2 hst
  have hj : 0 ≤ (j : ℝ) * ((t - s) / ((n + 1 : ℕ) : ℝ)) := by positivity
  have hj1 : 0 ≤ ((j : ℝ) + 1) * ((t - s) / ((n + 1 : ℕ) : ℝ)) := by positivity
  rw [hH _ (le_add_of_nonneg_right hj), add_sub_cancel_left, wnnIncr_shift B hs _ hj hj1]

lemma itoRiemann_process_congr (B : MultiBrownian Ω P d) (k : Fin d) {G G' : ℝ → Ω → ℝ}
    {s t : ℝ} {ω : Ω} (hG : ∀ r, s ≤ r → G r ω = G' r ω) (hst : s ≤ t) (n : ℕ) :
    itoRiemann_process B k G s t n ω = itoRiemann_process B k G' s t n ω := by
  simp only [itoRiemann_process]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 := sub_nonneg.2 hst
  rw [hG _ (le_add_of_nonneg_right (by positivity))]

lemma itoRiemann_process_sum_mul (B : MultiBrownian Ω P d) (k : Fin d) (S : Finset ℕ)
    (F : ℕ → ℝ → Ω → ℝ) (c : ℕ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemann_process B k (fun r ω => ∑ i ∈ S, F i r ω * c i ω) s t n ω =
      ∑ i ∈ S, itoRiemann_process B k (F i) s t n ω * c i ω := by
  simp only [itoRiemann_process, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma itoRiemann_process_one (B : MultiBrownian Ω P d) (k : Fin d) {s t : ℝ} (n : ℕ)
    (ω : Ω) : itoRiemann_process B k (fun _ _ => 1) s t n ω = wnnIncr B k s t ω := by
  have h := Finset.sum_range_sub (fun j : ℕ =>
    MultiBrownian.W B (s + (j : ℝ) * ((t - s) / ((n + 1 : ℕ) : ℝ))) ω k) (n + 1)
  have hN : s + ((n + 1 : ℕ) : ℝ) * ((t - s) / ((n + 1 : ℕ) : ℝ)) = t := by
    field_simp; ring
  simp only [hN, Nat.cast_zero, zero_mul, add_zero] at h
  simp only [itoRiemann_process, one_mul, wnnIncr_eq_W]
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring_nf

lemma offRiemann_succ (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ)
    (ω : Ω) : offRiemann B k H s t (n + 1) ω = itoRiemann_process B k H s t n ω := by
  simp only [offRiemann, itoRiemann_process]
  push_cast
  rfl

/-- Riemann sums of an `s`-start word coordinate converge a.s. to the next letter. -/
lemma ae_tendsto_itoRiemann_start (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s) (k : Fin d)
    (A : Word (d + 1)) {t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => itoRiemann_process B k (fun r ω' => itoWordIntegral B s r ω' A)
      s t n ω) atTop (𝓝 (itoWordIntegral B s t ω (k.succ :: A))) := by
  by_cases hA : A = []
  · subst hA
    refine ae_of_all _ fun ω => ?_
    simp only [itoWordIntegral_empty, itoRiemann_process_one, itoWordIntegral_space, wnnIncr_eq_W]
    exact tendsto_const_nhds
  set B' := B.shift s.toNNReal
  have ht' := sub_nonneg.2 hst
  obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B' ht' A hA).holderAdaptedEven le_rfl
  have h1 := (itoIntegral_process_of_holderAdapted B' k (hH.toHolderAdapted le_rfl) ht').1
  filter_upwards [h1, ae_itoWordIntegral_space_cons B' ht' k hA ht' le_rfl,
    ae_itoWordIntegral_shift B hs A, ae_itoWordIntegral_shift B hs (k.succ :: A)]
    with ω h1 h2 h3 h4
  rw [h4 t hst, h2]
  refine h1.congr fun n => ?_
  rw [← itoRiemann_process_eq_unifRiemann, itoRiemann_process_shift B hs k
    (H' := fun x ω' => itoWordIntegral B' 0 x ω' A) (fun r hr => h3 r hr) hst]

/-- Time integrals of `s`-start word coordinates are the next (time) letter. -/
lemma ae_integral_itoWordIntegral_start (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s)
    (A : Word (d + 1)) {t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, ∫ r in s..t, itoWordIntegral B s r ω A =
      itoWordIntegral B s t ω ((0 : Fin (d + 1)) :: A) := by
  set B' := B.shift s.toNNReal
  filter_upwards [ae_itoWordIntegral_shift B hs A, ae_itoWordIntegral_shift B hs (0 :: A),
    ae_itoWordIntegral_time_cons B' (sub_nonneg.2 hst)] with ω h3 h4 h5
  rw [h4 t hst, h5 A, intervalIntegral.integral_congr
    (g := fun r => itoWordIntegral B' 0 (r - s) ω A) fun r hr => h3 r (by
      rw [uIcc_of_le hst] at hr; exact hr.1),
    intervalIntegral.integral_comp_sub_right (fun x => itoWordIntegral B' 0 x ω A) s, sub_self]

/-! ## Chen's identity for the Itô word integrals -/

section ItoChen

variable (B : MultiBrownian Ω P d) {s : ℝ} {K : Word (d + 1)}

/-- Chen step, time letter. -/
theorem ae_chen_time_step (hs : 0 ≤ s) {t : ℝ} (hst : s ≤ t)
    (ih : ∀ᵐ ω ∂P, ∀ r, s ≤ r → itoWordIntegral B 0 r ω K =
      chenSum (fun A => itoWordIntegral B s r ω A) (fun C => itoWordIntegral B 0 s ω C) K) :
    ∀ᵐ ω ∂P, itoWordIntegral B 0 t ω ((0 : Fin (d + 1)) :: K) =
      chenSum (fun A => itoWordIntegral B s t ω A) (fun C => itoWordIntegral B 0 s ω C)
        ((0 : Fin (d + 1)) :: K) := by
  have ht0 := hs.trans hst
  filter_upwards [ih, ae_itoWordIntegral_time_cons B ht0, ae_itoWordIntegral_time_cons B hs,
    ae_continuousOn_itoWordIntegral B ht0, ae_continuousOn_itoWordIntegral_start B hs,
    ae_all_iff.2 fun i : ℕ => ae_integral_itoWordIntegral_start B hs (K.take i) hst]
    with ω hih h0t h0s hc hcs hint
  rw [chenSum_cons, h0t K, h0s K, itoWordIntegral_empty, one_mul]
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have hii : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      IntervalIntegrable (fun r => itoWordIntegral B 0 r ω K) volume a b :=
    fun a b ha hab hbt => ((hc K).mono (Icc_subset_Icc ha hbt)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 s le_rfl hs hst)
    (hii s t hs hst le_rfl)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun r => ∑ i ∈ Finset.range (K.length + 1),
      itoWordIntegral B s r ω (K.take i) * itoWordIntegral B 0 s ω (K.drop i))
    (fun r hr => by rw [uIcc_of_le hst] at hr; exact hih r hr.1)]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (((hcs N _).mono (Icc_subset_Icc le_rfl hN)).intervalIntegrable_of_Icc hst).mul_const _]
  unfold chenSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_mul_const, hint i]

/-- Chen step, Brownian letter: additivity of the Itô integral at `s` (grid change) and the
restart identity for the integrands over `[s, t]`. -/
theorem ae_chen_space_step (hs : 0 ≤ s) {t : ℝ} (hst : s < t) (k : Fin d) (hK : K ≠ [])
    (ih : ∀ᵐ ω ∂P, ∀ r, s ≤ r → itoWordIntegral B 0 r ω K =
      chenSum (fun A => itoWordIntegral B s r ω A) (fun C => itoWordIntegral B 0 s ω C) K) :
    ∀ᵐ ω ∂P, itoWordIntegral B 0 t ω (k.succ :: K) =
      chenSum (fun A => itoWordIntegral B s t ω A) (fun C => itoWordIntegral B 0 s ω C)
        (k.succ :: K) := by
  have ht0 : 0 ≤ t := hs.trans hst.le
  obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B ht0 K hK).holderAdaptedEven le_rfl
  obtain ⟨K₀, hHA⟩ : ∃ K₀, HolderAdapted B (fun r ω => itoWordIntegral B 0 r ω K) t K₀ :=
    ⟨_, hH.toHolderAdapted le_rfl⟩
  obtain ⟨K₁, hHAs⟩ : ∃ K₁, HolderAdapted B (fun r ω => itoWordIntegral B 0 r ω K) s K₁ :=
    ⟨_, (hH.mono hst.le).toHolderAdapted le_rfl⟩
  have hmU : ∀ x N, Measurable (unifRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) x N) :=
    fun x N => Finset.measurable_sum _ fun i _ =>
      (measurable_itoWordIntegral B 0 _ K).mul (measurable_wnnIncr B k _ _)
  have hmO : ∀ N, Measurable (offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t N) :=
    fun N => Finset.measurable_sum _ fun i _ =>
      (measurable_itoWordIntegral B 0 _ K).mul (measurable_wnnIncr B k _ _)
  have hUt := tendstoInMeasure_of_tendsto_ae (fun n => (hmU t (n + 1)).aestronglyMeasurable)
    (itoIntegral_process_of_holderAdapted B k hHA ht0).1
  have hUs := tendstoInMeasure_of_tendsto_ae (fun n => (hmU s (n + 1)).aestronglyMeasurable)
    (itoIntegral_process_of_holderAdapted B k hHAs hs).1
  have hE : TendstoInMeasure P (fun n ω =>
      unifRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) t (n + 1) ω -
        unifRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s (n + 1) ω -
        offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t (n + 1) ω) atTop
      (fun _ => 0) := by
    have hgc := fun n : ℕ => integral_gridChange_le B k hHA hs hst le_rfl (N := n + 1) n.succ_pos
    have hmE : ∀ n : ℕ, AEStronglyMeasurable (fun ω =>
        unifRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) t (n + 1) ω -
          unifRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s (n + 1) ω -
          offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t (n + 1) ω) P :=
      fun n => (((hmU t _).sub (hmU s _)).sub (hmO _)).aestronglyMeasurable
    refine tendstoInMeasure_zero_of_integral_sq_le
      (fun n => memLp_two_of_integrable_sq (hmE n)
        (integrable_sq_of_integrable_pow_four (hmE n) (hgc n).1))
      (b := fun n => Real.sqrt (16 * gaussFourthConst *
        (Real.sqrt K₀ * (t / ((n + 1 : ℕ) : ℝ)) * t) ^ 2))
      (fun n => (integral_sq_le_sqrt_four (hmE n) (hgc n).1).trans
        (Real.sqrt_le_sqrt (hgc n).2)) ?_
    have hx : Tendsto (fun n : ℕ => t / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_div_succ t
    have hφ : Continuous fun x : ℝ =>
        Real.sqrt (16 * gaussFourthConst * (Real.sqrt K₀ * x * t) ^ 2) := by fun_prop
    simpa [Function.comp_def] using (hφ.tendsto 0).comp hx
  have hO : TendstoInMeasure P
      (fun n ω => offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t (n + 1) ω) atTop
      (fun ω => itoIntegral_process B k (fun r ω => itoWordIntegral B 0 r ω K) 0 t ω -
        itoIntegral_process B k (fun r ω => itoWordIntegral B 0 r ω K) 0 s ω) := by
    have h := tendstoInMeasure_sub' (tendstoInMeasure_sub' hUt hUs) hE
    exact tendstoInMeasure_congr_left (fun n ω => by ring)
      (tendstoInMeasure_congr_right (Eventually.of_forall fun ω => by simp only [sub_zero]) h)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n => offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t (n + 1) ω) atTop
      (𝓝 (∑ i ∈ Finset.range (K.length + 1),
        itoWordIntegral B s t ω (k.succ :: K.take i) * itoWordIntegral B 0 s ω (K.drop i))) := by
    filter_upwards [ih, ae_all_iff.2 fun i : ℕ =>
      ae_tendsto_itoRiemann_start B hs k (K.take i) hst.le] with ω hih hR
    have e : ∀ n, offRiemann B k (fun r ω => itoWordIntegral B 0 r ω K) s t (n + 1) ω =
        ∑ i ∈ Finset.range (K.length + 1), itoRiemann_process B k
          (fun r ω' => itoWordIntegral B s r ω' (K.take i)) s t n ω *
            itoWordIntegral B 0 s ω (K.drop i) := by
      intro n
      rw [offRiemann_succ, itoRiemann_process_congr B k
        (G' := fun r ω' => ∑ i ∈ Finset.range (K.length + 1),
          itoWordIntegral B s r ω' (K.take i) * itoWordIntegral B 0 s ω' (K.drop i))
        (fun r hr => hih r hr) hst.le]
      exact itoRiemann_process_sum_mul B k _ (fun i r ω' => itoWordIntegral B s r ω' (K.take i))
        (fun i ω' => itoWordIntegral B 0 s ω' (K.drop i)) s t n ω
    simp only [e]
    exact tendsto_finsetSum _ fun i _ => (hR i).mul_const _
  have hI := ae_eq_of_tendstoInMeasure_of_ae_tendsto hO hlim
  filter_upwards [hI, ae_itoWordIntegral_space_cons B ht0 k hK ht0 le_rfl,
    ae_itoWordIntegral_space_cons B ht0 k hK hs hst.le] with ω h1 h2 h3
  rw [chenSum_cons, itoWordIntegral_empty, one_mul, h2, h3]
  unfold chenSum
  linarith [h1]

/-- **Chen's identity for Itô word integrals** (a.s., simultaneously for all `t ≥ s`):
`I^K_{0,t} = Σ_{K = A C} I^A_{s,t} I^C_{0,s}` (the first letters of a word are the latest). -/
theorem ae_itoWordIntegral_chen (hs : 0 ≤ s) (K : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ t, s ≤ t → itoWordIntegral B 0 t ω K =
      chenSum (fun A => itoWordIntegral B s t ω A) (fun C => itoWordIntegral B 0 s ω C) K := by
  induction K with
  | nil => exact ae_of_all _ fun ω t _ => by simp [chenSum_nil, itoWordIntegral_empty]
  | cons j K ih =>
    refine ae_forall_of_continuousOn (f := fun t ω => itoWordIntegral B 0 t ω (j :: K))
      (g := fun t ω => chenSum (fun A => itoWordIntegral B s t ω A)
        (fun C => itoWordIntegral B 0 s ω C) (j :: K)) ?_ ?_ fun t hst => ?_
    · filter_upwards [ae_all_iff.2 fun N : ℕ =>
        ae_continuousOn_itoWordIntegral B (Nat.cast_nonneg N)] with ω h N
      exact (h N (j :: K)).mono (Icc_subset_Icc hs le_rfl)
    · filter_upwards [ae_continuousOn_itoWordIntegral_start B hs] with ω h N
      unfold chenSum
      exact continuousOn_finsetSum _ fun i _ => (h N _).mul continuousOn_const
    · by_cases hK : K = []
      · subst hK
        refine ae_of_all _ fun ω => ?_
        simp only [chenSum_cons, chenSum_nil, itoWordIntegral_empty, one_mul, mul_one]
        refine Fin.cases ?_ (fun i => ?_) j
        · simp only [itoWordIntegral_time]; ring
        · simp only [itoWordIntegral_space]; ring
      · refine Fin.cases ?_ (fun k => ?_) j
        · exact ae_chen_time_step B hs hst.le ih
        · exact ae_chen_space_step B hs hst k hK ih

end ItoChen

/-- **Chen's identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_chen (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B 0 t ω = paperSig2 B 0 s ω ⊗ₜ paperSig2 B s t ω := by
  sorry

/-- **Shuffle identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_shuffle (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (I J : Word (d + 1)) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff I * (paperSig2 B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (paperSig2 B 0 t ω) := by
  sorry

end SignatureVolatility
