module

public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics

@[expose] public section


open MeasureTheory Filter Topology Set
open scoped NNReal

namespace SignatureVolatility

/-!
# Restarting the Brownian motion at a time `s`

`B.shift s₀` is the Brownian motion `r ↦ W_{s₀ + r} - W_{s₀}` (weak Markov property,
Mathlib's `IsBrownianReal.shift`). Almost surely, simultaneously for all words and all upper
times, the Itô word integrals of `B` started at `s` equal those of `B.shift s` started at `0`
(`ae_itoWordIntegral_shift`). All `0`-start results (moments, continuity, dynamics) therefore
transfer to `s`-start word integrals, as needed for Chen's identity.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Brownian motion restarted at `s₀`: `W'_r = W_{s₀ + r} - W_{s₀}`. -/
def MultiBrownian.shift (B : MultiBrownian Ω P d) (s₀ : ℝ≥0) : MultiBrownian Ω P d where
  Wnn r ω i := B.Wnn (s₀ + r) ω i - B.Wnn s₀ ω i
  isBrownian i := (B.isBrownian i).shift s₀
  Wnn_zero ω i := by simp
  Wnn_meas r i := (B.Wnn_meas _ i).sub (B.Wnn_meas _ i)
  pathContinuous i ω :=
    ((B.pathContinuous i ω).comp (continuous_const.add continuous_id)).sub continuous_const
  coordsIndep := B.coordsIndep.comp (fun _ f r => f (s₀ + r) - f s₀) fun _ =>
    Measurable.of_eval fun r => (measurable_pi_apply (s₀ + r)).sub (measurable_pi_apply s₀)

lemma wnnIncr_shift (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s) (k : Fin d) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ω : Ω) :
    wnnIncr (B.shift s.toNNReal) k a b ω = wnnIncr B k (s + a) (s + b) ω := by
  simp only [wnnIncr, MultiBrownian.shift]
  rw [Real.toNNReal_add hs hb, Real.toNNReal_add hs ha]
  ring

lemma W_shift (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s) {r : ℝ} (hr : 0 ≤ r) (ω : Ω)
    (i : Fin d) :
    MultiBrownian.W (B.shift s.toNNReal) r ω i =
      MultiBrownian.W B (s + r) ω i - MultiBrownian.W B s ω i := by
  change (B.shift s.toNNReal).Wnn r.toNNReal ω i =
    B.Wnn (s + r).toNNReal ω i - B.Wnn s.toNNReal ω i
  simp only [MultiBrownian.shift]
  rw [Real.toNNReal_add hs hr]

/-- An Itô step vanishes at and before its start time. -/
lemma itoWordStep_of_le (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (H : ℝ → Ω → ℝ)
    {s q : ℝ} (hq : q ≤ s) (ω : Ω) : itoWordStep B j H s q ω = 0 := by
  unfold itoWordStep
  split_ifs with h
  · obtain rfl : q = s := le_antisymm hq h
    unfold itoWordIntegral_cons_long
    split_ifs with hj
    · simp only [lebIntegral_process, le_refl, ↓reduceDIte, lebRiemann_process, sub_self,
        zero_div, mul_zero, Finset.sum_const_zero]
      exact tendsto_const_nhds.limUnder_eq
    · simp only [itoIntegral_process, le_refl, ↓reduceDIte, itoRiemann_process, sub_self,
        zero_div, mul_zero, add_zero, wnnIncr, Finset.sum_const_zero]
      exact tendsto_const_nhds.limUnder_eq
  · rfl

lemma contVersion_itoWordStep_self (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    contVersion (itoWordStep B j H s) s ω = 0 :=
  contVersion_eq_of_tendsto (tendsto_const_nhds.congr fun n =>
    (itoWordStep_of_le B j H (dyadicFloor_le hs n) ω).symm)

/-- At a fixed time, the `0`-start Itô step is a.s. its continuous version. -/
lemma ae_itoWordStep_eq (B : MultiBrownian Ω P d) {u : ℝ} (hu : 0 ≤ u) (j : Fin (d + 1))
    {I : Word (d + 1)} (hI : I ≠ []) :
    (fun ω => itoWordStep B j (fun s ω' => itoWordIntegral B 0 s ω' I) 0 u ω) =ᵐ[P]
      fun ω => itoWordIntegral B 0 u ω (j :: I) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · filter_upwards [ae_itoWordIntegral_time_cons B hu, ae_continuousOn_itoWordIntegral B hu]
      with ω h0 hc
    rw [h0 I]
    have hj : ((0 : Fin (d + 1)) : ℕ) = 0 := rfl
    simp only [itoWordStep, itoWordIntegral_cons_long, hu, hj, ↓reduceIte, ↓reduceDIte]
    exact lebIntegral_process_eq_integral (T := u) hu le_rfl (hc I)
  · have hj : ((k.succ : Fin (d + 1)) : ℕ) ≠ 0 := by simp
    have hk : spaceLetterIndex k.succ hj = k := by ext; simp [spaceLetterIndex]
    filter_upwards [ae_itoWordIntegral_space_cons B hu k hI hu le_rfl] with ω hω
    rw [hω]
    simp [itoWordStep, itoWordIntegral_cons_long, hu, hk]

/-- **Restart identity.** Almost surely, for every upper time `r ≥ s`, the Itô word integral
of `B` over `[s, r]` is the word integral of the restarted motion over `[0, r - s]`. -/
theorem ae_itoWordIntegral_shift (B : MultiBrownian Ω P d) {s : ℝ} (hs : 0 ≤ s)
    (A : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ r, s ≤ r →
      itoWordIntegral B s r ω A = itoWordIntegral (B.shift s.toNNReal) 0 (r - s) ω A := by
  induction A with
  | nil => exact ae_of_all _ fun ω r _ => rfl
  | cons j A ih =>
    by_cases hA : A = []
    · subst hA
      refine ae_of_all _ fun ω r hr => ?_
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [itoWordIntegral_time]
      · rw [itoWordIntegral_space, itoWordIntegral_space, W_shift B hs (sub_nonneg.2 hr),
          W_shift B hs le_rfl]
        simp
    set B' := B.shift s.toNNReal
    set H : ℝ → Ω → ℝ := fun u ω' => itoWordIntegral B s u ω' A
    set H' : ℝ → Ω → ℝ := fun u ω' => itoWordIntegral B' 0 u ω' A
    have hstep : ∀ ω, (∀ r, s ≤ r → H r ω = H' (r - s) ω) → ∀ q, s ≤ q →
        itoWordStep B j H s q ω = itoWordStep B' j H' 0 (q - s) ω := by
      intro ω hH q hq
      have hq' : 0 ≤ q - s := sub_nonneg.2 hq
      simp only [itoWordStep, hq, hq', ↓reduceIte, itoWordIntegral_cons_long]
      split_ifs with hj
      · simp only [lebIntegral_process, hq, hq', ↓reduceDIte]
        congr 1; funext n
        simp only [lebRiemann_process, sub_zero, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : 0 ≤ (k : ℝ) * ((q - s) / ((n + 1 : ℕ) : ℝ)) := by positivity
        rw [hH _ (le_add_of_nonneg_right hk), add_sub_cancel_left]
      · simp only [itoIntegral_process, hq, hq', ↓reduceDIte]
        congr 1; funext n
        simp only [itoRiemann_process, sub_zero, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : 0 ≤ (k : ℝ) * ((q - s) / ((n + 1 : ℕ) : ℝ)) := by positivity
        have hk1 : 0 ≤ ((k : ℝ) + 1) * ((q - s) / ((n + 1 : ℕ) : ℝ)) := by positivity
        rw [hH _ (le_add_of_nonneg_right hk), add_sub_cancel_left, wnnIncr_shift B hs _ hk hk1]
    have hdy : ∀ᵐ ω ∂P, ∀ n m : ℕ, s ≤ (m : ℝ) / 2 ^ n →
        itoWordStep B' j H' 0 ((m : ℝ) / 2 ^ n - s) ω =
          itoWordIntegral B' 0 ((m : ℝ) / 2 ^ n - s) ω (j :: A) := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro m
      by_cases h : s ≤ (m : ℝ) / 2 ^ n
      · filter_upwards [ae_itoWordStep_eq B' (sub_nonneg.2 h) j hA] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω h' => absurd h' h
    have hcont : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ J : Word (d + 1),
        ContinuousOn (fun x => itoWordIntegral B' 0 x ω J) (Icc 0 N) :=
      ae_all_iff.2 fun N => ae_continuousOn_itoWordIntegral B' (Nat.cast_nonneg N)
    filter_upwards [ih, hdy, hcont] with ω hih hd hc r hr
    have eL : itoWordIntegral B s r ω (j :: A) = contVersion (itoWordStep B j H s) r ω := by
      simp [itoWordIntegral, hA, H]
    rcases hr.eq_or_lt with rfl | hlt
    · have eR : itoWordIntegral B' 0 0 ω (j :: A) = contVersion (itoWordStep B' j H' 0) 0 ω := by
        simp [itoWordIntegral, hA, H']
      rw [eL, sub_self, eR, contVersion_itoWordStep_self B j H hs ω,
        contVersion_itoWordStep_self B' j H' le_rfl ω]
    · rw [eL]
      apply contVersion_eq_of_tendsto
      obtain ⟨N, hN⟩ := exists_nat_ge r
      have hr0 : 0 ≤ r := hs.trans hr
      have hev := (tendsto_dyadicFloor hr0).eventually (lt_mem_nhds hlt)
      have hlim : Tendsto (fun n => dyadicFloor n r - s) atTop (𝓝[Icc 0 (N : ℝ)] (r - s)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyadicFloor hr0).sub_const s, ?_⟩
        filter_upwards [hev] with n hn
        exact ⟨by linarith, by linarith [dyadicFloor_le hr0 n]⟩
      have hmem : r - s ∈ Icc 0 (N : ℝ) := ⟨sub_nonneg.2 hr, by linarith⟩
      refine ((hc N (j :: A) (r - s) hmem).tendsto.comp hlim).congr' ?_
      filter_upwards [hev] with n hn
      simp only [Function.comp_apply]
      rw [hstep ω hih _ hn.le]
      exact (hd n ⌊r * 2 ^ n⌋₊ hn.le).symm

end SignatureVolatility
