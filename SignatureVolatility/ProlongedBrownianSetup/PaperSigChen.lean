module

public import SignatureVolatility.ProlongedBrownianSetup.ShiftedWordIntegral
public import SignatureVolatility.ExtTensorAlgebra.TensorExpShuffle

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

/-! ## Contraction expansions respect deconcatenation -/

section StratChen

/-- Contraction (Stratonovich-from-Itô) expansion of a word functional. -/
def stratC (X : Word (d + 1) → ℝ) (K : Word (d + 1)) : ℝ :=
  ((contractions K).map (fun p => p.1 * X p.2)).sum

lemma stratC_nil (X : Word (d + 1) → ℝ) : stratC X [] = X [] := by
  simp [stratC, contractions]

lemma stratC_cons (X : Word (d + 1) → ℝ) (j : Fin (d + 1)) (K : Word (d + 1)) :
    stratC X (j :: K) = stratC (fun w => X (j :: w)) K +
      if K.head? = some j ∧ (j : ℕ) ≠ 0 then
        (1 / 2 : ℝ) * stratC (fun w => X ((0 : Fin (d + 1)) :: w)) K.tail else 0 := by
  unfold stratC
  rw [contractions_cons, List.map_append, List.sum_append, List.map_map]
  congr 1
  split_ifs
  · rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    ring
  · simp

lemma stratC_add_mul (a : ℝ) (X Y : Word (d + 1) → ℝ) (K : Word (d + 1)) :
    stratC (fun w => a * X w + Y w) K = a * stratC X K + stratC Y K := by
  unfold stratC
  induction contractions K with
  | nil => simp
  | cons p L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma chenSum_add_left (X Y H : Word (d + 1) → ℝ) (K : Word (d + 1)) :
    chenSum (fun A => X A + Y A) H K = chenSum X H K + chenSum Y H K := by
  unfold chenSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma chenSum_ite_head (Z H : Word (d + 1) → ℝ) (j : Fin (d + 1)) (c : Prop) [Decidable c]
    (K : Word (d + 1)) :
    chenSum (fun A => if A.head? = some j ∧ c then (1 / 2 : ℝ) * Z A.tail else 0) H K =
      if K.head? = some j ∧ c then (1 / 2 : ℝ) * chenSum Z H K.tail else 0 := by
  cases K with
  | nil => simp [chenSum]
  | cons l K =>
    rw [chenSum_cons]
    simp only [List.head?_nil, List.head?_cons, List.tail_cons, reduceCtorEq, false_and,
      ite_false, zero_mul, zero_add, Option.some.injEq]
    by_cases h : l = j ∧ c
    · simp only [h, and_self, ite_true]
      unfold chenSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [h, ite_false]
      unfold chenSum
      simp

lemma stratC_chenSum_cons (G H : Word (d + 1) → ℝ) (l : Fin (d + 1)) (K : Word (d + 1)) :
    stratC (fun w => chenSum G H (l :: w)) K =
      G [] * stratC (fun w => H (l :: w)) K + stratC (fun w => chenSum (fun A => G (l :: A)) H w) K := by
  rw [show (fun w => chenSum G H (l :: w)) = fun w =>
      G [] * H (l :: w) + chenSum (fun A => G (l :: A)) H w from funext fun w => chenSum_cons G H l w,
    stratC_add_mul]

/-- **The contraction expansion is a deconcatenation morphism.** -/
theorem stratC_chenSum : ∀ (K : Word (d + 1)) (G H : Word (d + 1) → ℝ),
    stratC (fun w => chenSum G H w) K = chenSum (stratC G) (stratC H) K
  | [], G, H => by simp [stratC_nil, chenSum_nil]
  | j :: K, G, H => by
    have e2 : (fun A => stratC G (j :: A)) = fun A => stratC (fun w => G (j :: w)) A +
        (if A.head? = some j ∧ (j : ℕ) ≠ 0 then
          (1 / 2 : ℝ) * stratC (fun w => G ((0 : Fin (d + 1)) :: w)) A.tail else 0) :=
      funext fun A => stratC_cons G j A
    rw [stratC_cons, chenSum_cons (stratC G) (stratC H), stratC_chenSum_cons,
      stratC_chenSum_cons, stratC_chenSum K (fun A => G (j :: A)) H,
      stratC_chenSum K.tail (fun A => G ((0 : Fin (d + 1)) :: A)) H, e2, chenSum_add_left,
      chenSum_ite_head, stratC_nil, stratC_cons H j K]
    split_ifs <;> ring
  termination_by K _ _ => K.length
  decreasing_by
    all_goals simp only [List.length_cons, List.length_tail]
    all_goals omega

lemma chenSum_reverse (G H : Word (d + 1) → ℝ) (I : Word (d + 1)) :
    chenSum G H I.reverse = ∑ k ∈ Finset.range (I.length + 1),
      H ((I.take k).reverse) * G ((I.drop k).reverse) := by
  unfold chenSum
  rw [List.length_reverse, ← Finset.sum_range_reflect
    (fun k => H ((I.take k).reverse) * G ((I.drop k).reverse)) (I.length + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [List.take_reverse, List.drop_reverse]
  have e : I.length - k = I.length + 1 - 1 - k := by omega
  rw [e, mul_comm]

end StratChen

/-- **Chen's identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_chen (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B 0 t ω = paperSig2 B 0 s ω ⊗ₜ paperSig2 B s t ω := by
  have hito : ∀ᵐ ω ∂P, ∀ K : Word (d + 1), itoWordIntegral B 0 t ω K =
      chenSum (fun A => itoWordIntegral B s t ω A) (fun C => itoWordIntegral B 0 s ω C) K :=
    ae_all_iff.2 fun K => (ae_itoWordIntegral_chen B hs K).mono fun ω h => h t hst
  filter_upwards [hito] with ω h
  ext I
  show (paperSig2 B 0 t ω).coeff I = ∑ k ∈ Finset.range (I.length + 1),
    (paperSig2 B 0 s ω).coeff (I.take k) * (paperSig2 B s t ω).coeff (I.drop k)
  rw [paperSig2_coeff, stratWordIntegral_eq_list]
  change stratC (fun w => itoWordIntegral B 0 t ω w) I.reverse = _
  rw [show (fun w => itoWordIntegral B 0 t ω w) = fun w => chenSum
      (fun A => itoWordIntegral B s t ω A) (fun C => itoWordIntegral B 0 s ω C) w from funext h,
    stratC_chenSum, chenSum_reverse]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [paperSig2_coeff, paperSig2_coeff, stratWordIntegral_eq_list, stratWordIntegral_eq_list]
  rfl

/-! ## Shuffle

The shuffle defect `Ŵ^I Ŵ^J - ⟨Ŵ, I ⧢ J⟩` of a pair of total length `n` is additive over a
partition once all shorter pairs are known to be shuffle-compatible (Chen +
`concat_shuffle_defect`). Each cell's defect has `L¹` size `O(Δ^{n/2})` by the level moment
bounds, so for `n ≥ 3` the sum over `N` cells is `O(N^{-1/2})` and the defect vanishes. The
pair case `n = 2` is integration by parts: the two trapezoid sums add up exactly to
`Ŵ^i Ŵ^j`, and `paperSig2_dynamics` identifies their limits. -/

section Shuffle

open ExtTensorAlgebra

/-- Shuffle defect of `X` on the pair `(I, J)`. -/
def shDef (X : ExtTensorAlgebra (d + 1)) (I J : Word (d + 1)) : ℝ :=
  X.coeff I * X.coeff J - evalShuffleBasis I J X

/-! ### Exponent bookkeeping -/

lemma wordExp_append : ∀ A C : Word (d + 1), wordExp (A ++ C) = wordExp A + wordExp C
  | [], C => by simp [wordExp]
  | j :: A, C => by
    simp only [List.cons_append, wordExp, wordExp_append A C]
    omega

lemma wordExp_reverse : ∀ A : Word (d + 1), wordExp A.reverse = wordExp A
  | [] => rfl
  | j :: A => by
    rw [List.reverse_cons, wordExp_append, wordExp_reverse A]
    simp [wordExp]

lemma wordExp_of_mem_shuffleWords : ∀ (I J K : Word (d + 1)), K ∈ shuffleWords I J →
    wordExp K = wordExp I + wordExp J
  | [], J, K, h => by
    simp [shuffleWords] at h; subst h; simp [wordExp]
  | i :: I, [], K, h => by
    simp [shuffleWords] at h; subst h; simp [wordExp]
  | i :: I, j :: J, K, h => by
    simp only [shuffleWords, List.mem_append, List.mem_map] at h
    rcases h with ⟨K', hK', rfl⟩ | ⟨K', hK', rfl⟩
    · have := wordExp_of_mem_shuffleWords I (j :: J) K' hK'
      simp only [wordExp] at this ⊢
      omega
    · have := wordExp_of_mem_shuffleWords (i :: I) J K' hK'
      simp only [wordExp] at this ⊢
      omega
  termination_by I J _ _ => I.length + J.length

lemma wordExp_of_mem_contractions_aux : ∀ (n : ℕ) (K : Word (d + 1)), K.length ≤ n →
    ∀ p ∈ contractions K, wordExp p.2 = wordExp K
  | 0, K, h, p, hp => by
    have : K = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [contractions] at hp
    simp [hp]
  | n + 1, [], _, p, hp => by
    simp [contractions] at hp
    simp [hp]
  | n + 1, j :: K, h, p, hp => by
    have hK : K.length ≤ n := by simp at h; omega
    rw [contractions_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      simp only [wordExp, wordExp_of_mem_contractions_aux n K hK q hq]
    · split_ifs at hp with hc
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        have hKt : K.tail.length ≤ n := by simp; omega
        have e := wordExp_of_mem_contractions_aux n K.tail hKt q hq
        obtain ⟨hh, hj⟩ := hc
        cases K with
        | nil => simp at hh
        | cons j' K =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          simp only [List.tail_cons] at e
          simp only [wordExp, e, letterExp, hj, ite_false, Fin.val_zero, ite_true]
      · simp at hp

lemma wordExp_of_mem_contractions {K : Word (d + 1)} {p : ℝ × Word (d + 1)}
    (hp : p ∈ contractions K) : wordExp p.2 = wordExp K :=
  wordExp_of_mem_contractions_aux K.length K le_rfl p hp

/-! ### Second moments of the coordinates -/

lemma integral_sq_itoWordIntegral_le (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s)
    (w : Word (d + 1)) :
    ∫ ω, itoWordIntegral B 0 s ω w ^ 2 ∂P ≤ |wordConst 2 w| * s ^ wordExp w := by
  by_cases hw : w = []
  · subst hw; simp [itoWordIntegral_empty, wordConst, wordExp]
  · have hX := levelBound_itoWordIntegral B hs w hw
    have h4 := integrable_pow_of_memLp_four (k := 4)
      (by simpa using memLp_itoWordIntegral B hs w (le_refl 2)) le_rfl
    refine (integral_sq_le_sqrt_four (measurable_itoWordIntegral B 0 s w).aestronglyMeasurable
      h4).trans ?_
    have := hX.mom 2 (le_refl 2) s hs le_rfl
    have h' : Real.sqrt (∫ ω, itoWordIntegral B 0 s ω w ^ 4 ∂P) ≤ wordConst 2 w * s ^ wordExp w := by
      simpa [nrm, Real.sqrt_eq_rpow] using this
    exact h'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hs _))

/-- Constant in the second-moment bound of the Stratonovich coordinate `K` (Itô order). -/
def stratConst (K : Word (d + 1)) : ℝ :=
  (contractions K).length * ∑ i : Fin (contractions K).length, |wordConst 2 (contractions K)[i.1].2|

lemma stratConst_nonneg (K : Word (d + 1)) : 0 ≤ stratConst K :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma integral_sq_paperSig2_le (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s)
    (I : Word (d + 1)) :
    ∫ ω, (paperSig2 B 0 s ω).coeff I ^ 2 ∂P ≤ stratConst I.reverse * s ^ wordExp I := by
  obtain ⟨L, hL⟩ : ∃ L, L = contractions I.reverse := ⟨_, rfl⟩
  have hX : ∀ i : Fin L.length,
      Integrable (fun ω => itoWordIntegral B 0 s ω L[i.1].2 ^ 2) P := fun i =>
    integrable_pow_of_memLp_four (by simpa using memLp_itoWordIntegral B hs L[i.1].2 (le_refl 2))
      (by norm_num)
  have hmem : ∀ i : Fin L.length, L[i.1] ∈ contractions I.reverse := fun i => by
    rw [← hL]; exact List.getElem_mem i.2
  have hpt : ∀ ω, (paperSig2 B 0 s ω).coeff I ^ 2 ≤
      L.length * ∑ i : Fin L.length, itoWordIntegral B 0 s ω L[i.1].2 ^ 2 := by
    intro ω
    rw [paperSig2_coeff, stratWordIntegral_eq_list, ← hL,
      ← Fin.sum_univ_fun_getElem L (fun p => p.1 * itoWordIntegral B 0 s ω p.2)]
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    obtain ⟨h0, h1, -, -⟩ := mem_contractions (hmem i)
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  calc ∫ ω, (paperSig2 B 0 s ω).coeff I ^ 2 ∂P
      ≤ ∫ ω, (L.length : ℝ) * ∑ i : Fin L.length, itoWordIntegral B 0 s ω L[i.1].2 ^ 2 ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          ((integrable_finsetSum _ fun i _ => hX i).const_mul _) (Eventually.of_forall hpt)
    _ = (L.length : ℝ) * ∑ i : Fin L.length, ∫ ω, itoWordIntegral B 0 s ω L[i.1].2 ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hX i]
    _ ≤ (L.length : ℝ) * ∑ i : Fin L.length, |wordConst 2 L[i.1].2| * s ^ wordExp I := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        have e : wordExp L[i.1].2 = wordExp I := by
          rw [wordExp_of_mem_contractions (hmem i), wordExp_reverse]
        rw [← e]
        exact integral_sq_itoWordIntegral_le B hs _
    _ = stratConst I.reverse * s ^ wordExp I := by
        subst hL
        rw [stratConst, ← Finset.sum_mul, mul_assoc]

omit [IsProbabilityMeasure P] in
lemma integral_abs_mul_le_sqrt {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ∫ ω, |X ω| * |Y ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
  have h := abs_integral_mul_le_sqrt hX.abs hY.abs
  simp only [Pi.abs_apply, sq_abs] at h
  exact (le_abs_self _).trans h

lemma integral_abs_le_sqrt {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, |X ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt hX (memLp_const (1 : ℝ))
  simpa using h

/-! ### Size of one cell's defect -/

/-- Constant in the `L¹` bound of the shuffle defect. -/
def shConst (I J : Word (d + 1)) : ℝ :=
  Real.sqrt (stratConst I.reverse) * Real.sqrt (stratConst J.reverse) +
    ∑ k : Fin (shuffleWords I J).length, Real.sqrt (stratConst ((shuffleWords I J)[k.1]).reverse)

lemma shConst_nonneg (I J : Word (d + 1)) : 0 ≤ shConst I J :=
  add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

lemma measurable_shDef (B : MultiBrownian Ω P d) (s u : ℝ) (I J : Word (d + 1)) :
    Measurable fun ω => shDef (paperSig2 B s u ω) I J := by
  unfold shDef evalShuffleBasis
  simp_rw [← Fin.sum_univ_fun_getElem (shuffleWords I J)]
  exact ((measurable_paperSig2_coeff B s u I).mul (measurable_paperSig2_coeff B s u J)).sub
    (Finset.measurable_sum _ fun k _ => measurable_paperSig2_coeff B s u _)

lemma abs_shDef_le (X : ExtTensorAlgebra (d + 1)) (I J : Word (d + 1)) :
    |shDef X I J| ≤ |X.coeff I| * |X.coeff J| +
      ∑ k : Fin (shuffleWords I J).length, |X.coeff (shuffleWords I J)[k.1]| := by
  rw [shDef, evalShuffleBasis, ← Fin.sum_univ_fun_getElem (shuffleWords I J)]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)

lemma integral_abs_shDef_le (B : MultiBrownian Ω P d) {Δ : ℝ} (hΔ : 0 ≤ Δ) (I J : Word (d + 1)) :
    Integrable (fun ω => shDef (paperSig2 B 0 Δ ω) I J) P ∧
    ∫ ω, |shDef (paperSig2 B 0 Δ ω) I J| ∂P ≤
      shConst I J * Real.sqrt (Δ ^ (wordExp I + wordExp J)) := by
  have hm : ∀ K, MemLp (fun ω => (paperSig2 B 0 Δ ω).coeff K) 2 P := fun K =>
    (memLp_paperSig2_coeff B hΔ K (le_refl 2)).mono_exponent (by norm_num)
  have hsq : ∀ K, Real.sqrt (∫ ω, (paperSig2 B 0 Δ ω).coeff K ^ 2 ∂P) ≤
      Real.sqrt (stratConst K.reverse) * Real.sqrt (Δ ^ wordExp K) := fun K => by
    rw [← Real.sqrt_mul (stratConst_nonneg _)]
    exact Real.sqrt_le_sqrt (integral_sq_paperSig2_le B hΔ K)
  have hint1 : Integrable (fun ω => |(paperSig2 B 0 Δ ω).coeff I| *
      |(paperSig2 B 0 Δ ω).coeff J|) P := by
    refine Integrable.mono' (((hm I).integrable_sq.add (hm J).integrable_sq).div_const 2)
      (((hm I).aestronglyMeasurable.norm.mul (hm J).aestronglyMeasurable.norm)) ?_
    refine Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|(paperSig2 B 0 Δ ω).coeff I| - |(paperSig2 B 0 Δ ω).coeff J|),
      sq_abs ((paperSig2 B 0 Δ ω).coeff I), sq_abs ((paperSig2 B 0 Δ ω).coeff J)]
  have hint2 : ∀ K, Integrable (fun ω => |(paperSig2 B 0 Δ ω).coeff K|) P := fun K =>
    ((hm K).integrable (by norm_num)).abs
  have hintS : Integrable (fun ω => ∑ k : Fin (shuffleWords I J).length, |(paperSig2 B 0 Δ ω).coeff (shuffleWords I J)[k.1]|) P :=
    integrable_finsetSum _ fun k _ => hint2 _
  have hbound := hint1.add hintS
  refine ⟨hbound.mono' (measurable_shDef B 0 Δ I J).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_shDef_le _ I J), ?_⟩
  have e : ∀ k : Fin (shuffleWords I J).length, wordExp (shuffleWords I J)[k.1] = wordExp I + wordExp J := fun k =>
    wordExp_of_mem_shuffleWords _ _ _ (List.getElem_mem (l := shuffleWords I J) k.2)
  calc ∫ ω, |shDef (paperSig2 B 0 Δ ω) I J| ∂P
      ≤ ∫ ω, (|(paperSig2 B 0 Δ ω).coeff I| * |(paperSig2 B 0 Δ ω).coeff J| +
          ∑ k : Fin (shuffleWords I J).length, |(paperSig2 B 0 Δ ω).coeff (shuffleWords I J)[k.1]|) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hbound
          (Eventually.of_forall fun ω => abs_shDef_le _ I J)
    _ = ∫ ω, |(paperSig2 B 0 Δ ω).coeff I| * |(paperSig2 B 0 Δ ω).coeff J| ∂P +
          ∑ k : Fin (shuffleWords I J).length, ∫ ω, |(paperSig2 B 0 Δ ω).coeff (shuffleWords I J)[k.1]| ∂P := by
        rw [integral_add hint1 hintS, integral_finsetSum _ fun k _ => hint2 _]
    _ ≤ (Real.sqrt (stratConst I.reverse) * Real.sqrt (Δ ^ wordExp I)) *
          (Real.sqrt (stratConst J.reverse) * Real.sqrt (Δ ^ wordExp J)) +
          ∑ k : Fin (shuffleWords I J).length, Real.sqrt (stratConst (shuffleWords I J)[k.1].reverse) *
            Real.sqrt (Δ ^ wordExp (shuffleWords I J)[k.1]) :=
        add_le_add ((integral_abs_mul_le_sqrt (hm I) (hm J)).trans
          (mul_le_mul (hsq I) (hsq J) (Real.sqrt_nonneg _) (by positivity)))
          (Finset.sum_le_sum fun k _ => (integral_abs_le_sqrt (hm _)).trans (hsq _))
    _ = shConst I J * Real.sqrt (Δ ^ (wordExp I + wordExp J)) := by
        simp only [e]
        rw [pow_add, Real.sqrt_mul (pow_nonneg hΔ _), shConst, add_mul, Finset.sum_mul]
        ring

/-! ### Restarting at `s` -/

theorem ae_paperSig2_shift (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B s t ω = paperSig2 (B.shift s.toNNReal) 0 (t - s) ω := by
  filter_upwards [ae_all_iff.2 fun A => ae_itoWordIntegral_shift B hs A] with ω h
  ext I
  rw [paperSig2_coeff, paperSig2_coeff, stratWordIntegral_eq_list, stratWordIntegral_eq_list]
  congr 1
  exact List.map_congr_left fun p _ => by rw [h p.2 t hst]

lemma integral_abs_shDef_le' (B : MultiBrownian Ω P d) {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u)
    (I J : Word (d + 1)) :
    Integrable (fun ω => shDef (paperSig2 B s u ω) I J) P ∧
    ∫ ω, |shDef (paperSig2 B s u ω) I J| ∂P ≤
      shConst I J * Real.sqrt ((u - s) ^ (wordExp I + wordExp J)) := by
  obtain ⟨hi, hb⟩ := integral_abs_shDef_le (B.shift s.toNNReal) (sub_nonneg.2 hsu) I J
  have he : (fun ω => shDef (paperSig2 (B.shift s.toNNReal) 0 (u - s) ω) I J) =ᵐ[P]
      fun ω => shDef (paperSig2 B s u ω) I J :=
    (ae_paperSig2_shift B hs hsu).mono fun ω h => by simp only; rw [h]
  refine ⟨hi.congr he, ?_⟩
  have he' : (fun ω => |shDef (paperSig2 (B.shift s.toNNReal) 0 (u - s) ω) I J|) =ᵐ[P]
      fun ω => |shDef (paperSig2 B s u ω) I J| := he.mono fun ω h => by
    simp only at h ⊢; rw [h]
  rw [← integral_congr_ae he']
  exact hb

/-! ### Induction on the total length -/

section Induction

variable {n : ℕ}
  (ih : ∀ m < n, ∀ (B : MultiBrownian Ω P d) (t : ℝ), 0 ≤ t → ∀ I J : Word (d + 1),
    I.length + J.length = m → ∀ᵐ ω ∂P, shDef (paperSig2 B 0 t ω) I J = 0)
include ih

lemma ae_lower_shuffle (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, ∀ I J : Word (d + 1), I.length + J.length < n →
      (paperSig2 B s t ω).coeff I * (paperSig2 B s t ω).coeff J =
        evalShuffleBasis I J (paperSig2 B s t ω) := by
  have h : ∀ I J : Word (d + 1), ∀ᵐ ω ∂P, I.length + J.length < n →
      shDef (paperSig2 (B.shift s.toNNReal) 0 (t - s) ω) I J = 0 := fun I J => by
    by_cases hIJ : I.length + J.length < n
    · exact (ih _ hIJ _ _ (sub_nonneg.2 hst) I J rfl).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hIJ
  filter_upwards [ae_paperSig2_shift B hs hst,
    ae_all_iff.2 fun I => ae_all_iff.2 (h I)] with ω he hω I J hIJ
  rw [he]
  exact sub_eq_zero.1 (hω I J hIJ)

lemma ae_shDef_grid (hn : 0 < n) (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    {I J : Word (d + 1)} (hIJ : I.length + J.length = n) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, shDef (paperSig2 B 0 (((k + 1 : ℕ) : ℝ) * t / N) ω) I J =
      ∑ m ∈ Finset.range (k + 1),
        shDef (paperSig2 B ((m : ℝ) * t / N) (((m + 1 : ℕ) : ℝ) * t / N) ω) I J := by
  have hg0 : ∀ k : ℕ, 0 ≤ (k : ℝ) * t / N := fun k => by positivity
  have hgm : ∀ k : ℕ, (k : ℝ) * t / N ≤ ((k + 1 : ℕ) : ℝ) * t / N := fun k =>
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht)
      (Nat.cast_nonneg N)
  intro k
  induction k with
  | zero => exact ae_of_all _ fun ω => by simp
  | succ k ihk =>
    filter_upwards [ihk, paperSig2_chen B (hg0 (k + 1)) (hgm (k + 1)),
      ae_lower_shuffle ih B le_rfl (hg0 (k + 1)),
      ae_lower_shuffle ih B (hg0 (k + 1)) (hgm (k + 1))] with ω h1 hc hl1 hl2
    rw [Finset.sum_range_succ, ← h1, hc]
    unfold shDef
    exact concat_shuffle_defect (paperSig2_empty _ _ _ _) (paperSig2_empty _ _ _ _) hl1 hl2
      hIJ hn

lemma ae_shDef_zero_step (hn : 3 ≤ n) (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    {I J : Word (d + 1)} (hIJ : I.length + J.length = n) :
    ∀ᵐ ω ∂P, shDef (paperSig2 B 0 t ω) I J = 0 := by
  set e := wordExp I + wordExp J with he
  have he3 : 3 ≤ e := by
    have := length_le_wordExp I; have := length_le_wordExp J; omega
  have hc0 := shConst_nonneg I J
  have key : ∀ N : ℕ, 1 ≤ N →
      ∫ ω, |shDef (paperSig2 B 0 t ω) I J| ∂P ≤ shConst I J * Real.sqrt (t ^ e / N) := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hgrid := ae_shDef_grid ih (by omega) B ht (N := N) hIJ (N - 1)
    rw [Nat.sub_add_cancel hN, mul_div_cancel_left₀ t hN0.ne'] at hgrid
    have hint : ∀ m ∈ Finset.range N, Integrable (fun ω =>
        shDef (paperSig2 B ((m : ℝ) * t / N) (((m + 1 : ℕ) : ℝ) * t / N) ω) I J) P :=
      fun m _ => (integral_abs_shDef_le' B (by positivity)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht)
          (Nat.cast_nonneg N)) I J).1
    have hcell : ∀ m ∈ Finset.range N, ∫ ω, |shDef (paperSig2 B ((m : ℝ) * t / N)
        (((m + 1 : ℕ) : ℝ) * t / N) ω) I J| ∂P ≤ shConst I J * Real.sqrt ((t / N) ^ e) := by
      intro m _
      have h := (integral_abs_shDef_le' B (s := (m : ℝ) * t / N)
        (u := ((m + 1 : ℕ) : ℝ) * t / N) (by positivity)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht)
          (Nat.cast_nonneg N)) I J).2
      have e1 : ((m + 1 : ℕ) : ℝ) * t / N - (m : ℝ) * t / N = t / N := by push_cast; ring
      rwa [e1] at h
    have hfin : (N : ℝ) * Real.sqrt ((t / N) ^ e) ≤ Real.sqrt (t ^ e / N) := by
      have hNe : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ e :=
        pow_le_pow_right₀ (by exact_mod_cast hN) he3
      have h2 : (N : ℝ) ^ 2 * (t / N) ^ e ≤ t ^ e / N := by
        rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) hN0]
        calc (N : ℝ) ^ 2 * t ^ e * N = t ^ e * N ^ 3 := by ring
          _ ≤ t ^ e * N ^ e := mul_le_mul_of_nonneg_left hNe (pow_nonneg ht e)
      calc (N : ℝ) * Real.sqrt ((t / N) ^ e)
          = Real.sqrt ((N : ℝ) ^ 2 * (t / N) ^ e) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN0.le]
        _ ≤ Real.sqrt (t ^ e / N) := Real.sqrt_le_sqrt h2
    calc ∫ ω, |shDef (paperSig2 B 0 t ω) I J| ∂P
        = ∫ ω, |∑ m ∈ Finset.range N, shDef (paperSig2 B ((m : ℝ) * t / N)
            (((m + 1 : ℕ) : ℝ) * t / N) ω) I J| ∂P :=
          integral_congr_ae (hgrid.mono fun ω h => by simp only [h])
      _ ≤ ∫ ω, ∑ m ∈ Finset.range N, |shDef (paperSig2 B ((m : ℝ) * t / N)
            (((m + 1 : ℕ) : ℝ) * t / N) ω) I J| ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_finsetSum _ fun m hm => (hint m hm).abs)
            (Eventually.of_forall fun ω => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ m ∈ Finset.range N, ∫ ω, |shDef (paperSig2 B ((m : ℝ) * t / N)
            (((m + 1 : ℕ) : ℝ) * t / N) ω) I J| ∂P :=
          integral_finsetSum _ fun m hm => (hint m hm).abs
      _ ≤ ∑ m ∈ Finset.range N, shConst I J * Real.sqrt ((t / N) ^ e) :=
          Finset.sum_le_sum hcell
      _ = shConst I J * ((N : ℝ) * Real.sqrt ((t / N) ^ e)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ shConst I J * Real.sqrt (t ^ e / N) := mul_le_mul_of_nonneg_left hfin hc0
  have hlim : Tendsto (fun N : ℕ => shConst I J * Real.sqrt (t ^ e / N)) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (t ^ e))).const_mul (shConst I J)
    simpa [Function.comp_def] using h
  have hle : ∫ ω, |shDef (paperSig2 B 0 t ω) I J| ∂P ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, key⟩)
  have hint := (integral_abs_shDef_le' B le_rfl ht I J).1
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) hint.abs).1
    (le_antisymm hle (integral_nonneg fun _ => abs_nonneg _))
  filter_upwards [h0] with ω hω
  simpa using hω

end Induction

/-! ### The pair case: integration by parts -/

lemma paperSig2_single_eq (B : MultiBrownian Ω P d) (u : ℝ) (ω : Ω) (i : Fin (d + 1)) :
    (paperSig2 B 0 u ω).coeff [i] =
      augCoord (MultiBrownian.W B) u ω i - augCoord (MultiBrownian.W B) 0 ω i := by
  rw [paperSig2_coeff, List.reverse_singleton]
  cases i using Fin.cases with
  | zero => simp [stratWordIntegral_time, augCoord]
  | succ i => simp [stratWordIntegral_space, augCoord]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma trapezoidSum_pair (W : ℝ → Ω → Fin d → ℝ) (Y Z : ℝ → Ω → ℝ) (i j : Fin (d + 1))
    (t : ℝ) (n : ℕ) (ω : Ω) (hY : ∀ u, Y u ω = augCoord W u ω i - augCoord W 0 ω i)
    (hZ : ∀ u, Z u ω = augCoord W u ω j - augCoord W 0 ω j) :
    trapezoidSum W Y j t n ω + trapezoidSum W Z i t n ω = Y t ω * Z t ω := by
  have hdi : ∀ u v, augCoord W v ω i - augCoord W u ω i = Y v ω - Y u ω := fun u v => by
    rw [hY u, hY v]; ring
  have hdj : ∀ u v, augCoord W v ω j - augCoord W u ω j = Z v ω - Z u ω := fun u v => by
    rw [hZ u, hZ v]; ring
  set f : ℕ → ℝ := fun k => Y ((k : ℝ) * t / ((n : ℝ) + 1)) ω * Z ((k : ℝ) * t / ((n : ℝ) + 1)) ω
  have hsum : trapezoidSum W Y j t n ω + trapezoidSum W Z i t n ω =
      ∑ k ∈ Finset.range (n + 1), (f (k + 1) - f k) := by
    unfold trapezoidSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hdi, hdj, f]
    push_cast
    ring
  rw [hsum, Finset.sum_range_sub]
  have e1 : (((n + 1 : ℕ) : ℝ)) * t / ((n : ℝ) + 1) = t := by
    push_cast; field_simp
  simp only [f, e1, Nat.cast_zero, zero_mul, zero_div]
  rw [hY 0]
  ring

lemma ae_shDef_pair (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (i j : Fin (d + 1)) :
    ∀ᵐ ω ∂P, shDef (paperSig2 B 0 t ω) [i] [j] = 0 := by
  have h := tendstoInMeasure_add' (paperSig2_dynamics B [i] j ht) (paperSig2_dynamics B [j] i ht)
  have hc : ∀ n ω, trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff [i])
      j t n ω + trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff [j])
      i t n ω = (paperSig2 B 0 t ω).coeff [i] * (paperSig2 B 0 t ω).coeff [j] := fun n ω =>
    trapezoidSum_pair _ _ _ i j t n ω (fun u => paperSig2_single_eq B u ω i)
      (fun u => paperSig2_single_eq B u ω j)
  have e := ae_eq_of_tendstoInMeasure_of_ae_tendsto h
    (G := fun ω => (paperSig2 B 0 t ω).coeff [i] * (paperSig2 B 0 t ω).coeff [j])
    (ae_of_all _ fun ω => tendsto_const_nhds.congr fun n => (hc n ω).symm)
  filter_upwards [e] with ω hω
  simp only [List.singleton_append] at hω
  simp [shDef, evalShuffleBasis, shuffleWords]
  linarith

theorem ae_shDef_eq_zero (n : ℕ) : ∀ (B : MultiBrownian Ω P d) (t : ℝ), 0 ≤ t →
    ∀ I J : Word (d + 1), I.length + J.length = n →
      ∀ᵐ ω ∂P, shDef (paperSig2 B 0 t ω) I J = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B t ht I J hIJ
  rcases I with _ | ⟨i, I⟩
  · exact ae_of_all _ fun ω => by simp [shDef, evalShuffleBasis, shuffleWords, paperSig2_empty]
  rcases J with _ | ⟨j, J⟩
  · exact ae_of_all _ fun ω => by simp [shDef, evalShuffleBasis, shuffleWords, paperSig2_empty]
  by_cases h2 : I = [] ∧ J = []
  · obtain ⟨rfl, rfl⟩ := h2
    exact ae_shDef_pair B ht i j
  have h1 : 1 ≤ I.length + J.length := by
    by_contra hc
    exact h2 ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
  simp only [List.length_cons] at hIJ
  exact ae_shDef_zero_step ih (by omega) B ht (I := i :: I) (J := j :: J)
    (by simp only [List.length_cons]; omega)

end Shuffle

/-- **Shuffle identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_shuffle (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (I J : Word (d + 1)) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff I * (paperSig2 B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (paperSig2 B 0 t ω) := by
  filter_upwards [ae_shDef_eq_zero _ B t ht I J rfl] with ω h
  exact sub_eq_zero.1 h

end SignatureVolatility
