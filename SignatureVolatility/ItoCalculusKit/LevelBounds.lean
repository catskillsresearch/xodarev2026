module

public import SignatureVolatility.ItoCalculusKit.LebIncrementEven
public import SignatureVolatility.ProlongedBrownianSetup.ContVersionKolmogorov

@[expose] public section

open MeasureTheory Filter Set

noncomputable section

namespace SignatureVolatility

/-!
# Level-wise `L^{2q}` bounds for the Itô word integrals

For every non-empty word `I` and every `q ≥ 2`, the Itô iterated integral
`X_u = itoWordIntegral B 0 u · I` on `[0, T]` is adapted, a.s. continuous, in `L^{2q}`, with

* `‖X_u‖_{2q}² ≤ wordConst q I · u ^ wordExp I`, and
* `‖X_v - X_u‖_{2q}² ≤ L (v - u)` for some `L`.

A time letter adds `2` to the (squared-norm) exponent and divides the constant by
`(q e + 1)^{1/q}`; an Itô letter adds `1` and divides by `e + 1`
(`levelBound_itoWordIntegral`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The level-wise bound package for a process `X` on `[0, T]`. -/
structure LevelBound (B : MultiBrownian Ω P d) (T : ℝ) (X : ℝ → Ω → ℝ) (e : ℕ)
    (A L : ℕ → ℝ) : Prop where
  A_nonneg : ∀ q, 2 ≤ q → 0 ≤ A q
  L_nonneg : ∀ q, 2 ≤ q → 0 ≤ L q
  meas : ∀ u, 0 ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg u] (X u)
  meas_all : ∀ u, Measurable (X u)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Icc 0 T)
  memLp : ∀ q, 2 ≤ q → ∀ u, 0 ≤ u → u ≤ T → MemLp (X u) (2 * q : ℕ) P
  mom : ∀ q, 2 ≤ q → ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, X u ω ^ (2 * q) ∂P) ≤ A q * u ^ e
  incr : ∀ q, 2 ≤ q → ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
    nrm q (∫ ω, (X v ω - X u ω) ^ (2 * q) ∂P) ≤ L q * (v - u)

/-- Squared-norm time exponent of a letter: `2` for time, `1` for a Brownian coordinate. -/
def letterExp (j : Fin (d + 1)) : ℕ := if (j : ℕ) = 0 then 2 else 1

/-- Squared-norm time exponent of a word. -/
def wordExp : Word (d + 1) → ℕ
  | [] => 0
  | j :: I => wordExp I + letterExp j

/-- The constant in the level-wise moment profile. -/
def wordConst (q : ℕ) : Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I = [] then (if (j : ℕ) = 0 then 1 else nrm q (gaussMoment q))
    else if (j : ℕ) = 0 then wordConst q I * nrm q (1 / ((q * wordExp I : ℕ) + 1 : ℝ))
    else itoEvenConst q * wordConst q I / (wordExp I + 1)

/-- The constant in the level-wise increment bound on `[0, T]`. -/
def wordIncr (q : ℕ) (T : ℝ) : Word (d + 1) → ℝ
  | [] => 0
  | j :: I =>
    if I = [] then (if (j : ℕ) = 0 then T else nrm q (gaussMoment q))
    else if (j : ℕ) = 0 then wordConst q I * T ^ wordExp I * T
    else itoEvenConst q * (wordConst q I * T ^ wordExp I)

omit [IsProbabilityMeasure P] in
lemma integral_ae_congr_pow {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = ∫ ω, Y ω ^ n ∂P :=
  integral_congr_ae (h.mono fun ω hω => by simp [hω])

/-- Kolmogorov transfer: bounds on a raw process pass to its continuous version. -/
theorem levelBound_contVersion (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T)
    {R : ℝ → Ω → ℝ} (hmeasR : ∀ u, Measurable (R u))
    (hadapt : ∀ u, 0 ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg u] (contVersion R u))
    {e : ℕ} {A L : ℕ → ℝ} (hA : ∀ q, 2 ≤ q → 0 ≤ A q) (hL : ∀ q, 2 ≤ q → 0 ≤ L q)
    (hLp : ∀ q, 2 ≤ q → ∀ u, 0 ≤ u → u ≤ T → MemLp (R u) (2 * q : ℕ) P)
    (hmom : ∀ q, 2 ≤ q → ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, R u ω ^ (2 * q) ∂P) ≤ A q * u ^ e)
    (hincr : ∀ q, 2 ≤ q → ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      nrm q (∫ ω, (R v ω - R u ω) ^ (2 * q) ∂P) ≤ L q * (v - u)) :
    LevelBound B T (contVersion R) e A L := by
  have hL4 := hL 4 (by norm_num)
  have hL4b := hincr 4 (by norm_num)
  have hK := contVersion_kolmogorov (P := P) (X := R) (C := L 4 ^ 4) hT (by positivity)
    (fun s _ _ => hmeasR s) (fun u v hu huv hvT => by
      have hm : MemLp (fun ω => R v ω - R u ω) (2 * 4 : ℕ) P :=
        (hLp 4 (by norm_num) v (hu.trans huv) hvT).sub (hLp 4 (by norm_num) u hu (huv.trans hvT))
      have hi := integrable_pow_of_memLp_evenDeg (N := 2 * 4) ⟨4, by norm_num⟩ hm
      refine ⟨by simpa using hi, ?_⟩
      have h0 : 0 ≤ ∫ ω, (R v ω - R u ω) ^ (2 * 4) ∂P :=
        integral_nonneg fun ω => Even.pow_nonneg ⟨4, by norm_num⟩ _
      have hb := hL4b u v hu huv hvT
      have := pow_le_pow_left₀ (nrm_nonneg 4 h0) hb 4
      rw [nrm_pow (by norm_num) h0, mul_pow] at this
      simpa using this)
  have hae : ∀ u, 0 ≤ u → u ≤ T → contVersion R u =ᵐ[P] R u := hK.2
  refine ⟨hA, hL, hadapt, fun u => measurable_contVersion R u fun n => hmeasR _, hK.1,
    fun q hq u hu huT => (hLp q hq u hu huT).ae_eq (hae u hu huT).symm,
    fun q hq u hu huT => ?_, fun q hq => ?_⟩
  · rw [integral_ae_congr_pow (hae u hu huT)]; exact hmom q hq u hu huT
  · intro u v hu huv hvT
    have hd : (fun ω => contVersion R v ω - contVersion R u ω) =ᵐ[P]
        fun ω => R v ω - R u ω := by
      filter_upwards [hae v (hu.trans huv) hvT, hae u hu (huv.trans hvT)] with ω h1 h2
      rw [h1, h2]
    rw [integral_ae_congr_pow hd]; exact hincr q hq u v hu huv hvT

lemma LevelBound.holderAdaptedEven {B : MultiBrownian Ω P d} {T : ℝ} {X : ℝ → Ω → ℝ} {e : ℕ}
    {A L : ℕ → ℝ} (hX : LevelBound B T X e A L) {q : ℕ} (hq : 2 ≤ q) :
    ∃ L, HolderAdaptedEven B q X T L :=
  ⟨L q, ⟨hX.L_nonneg q hq, hX.meas, hX.memLp q hq, hX.incr q hq⟩⟩

lemma LevelBound.mom_le_T {B : MultiBrownian Ω P d} {T : ℝ} {X : ℝ → Ω → ℝ} {e : ℕ}
    {A L : ℕ → ℝ} (hX : LevelBound B T X e A L) {q : ℕ} (hq : 2 ≤ q) :
    ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, X u ω ^ (2 * q) ∂P) ≤ A q * T ^ e := fun u hu huT =>
  (hX.mom q hq u hu huT).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huT e) (hX.A_nonneg q hq))

/-- **Itô letter step.** -/
theorem levelBound_itoStep (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) {X : ℝ → Ω → ℝ}
    {e : ℕ} {A L : ℕ → ℝ} (hX : LevelBound B T X e A L) (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0)
    (hadapt : ∀ u, 0 ≤ u → u ≤ T →
      Measurable[(pathFiltration B).σAlg u] (contVersion (itoWordStep B j X 0) u)) :
    LevelBound B T (contVersion (itoWordStep B j X 0)) (e + 1)
      (fun q => itoEvenConst q * A q / (e + 1)) (fun q => itoEvenConst q * (A q * T ^ e)) := by
  set k := spaceLetterIndex j hj
  have hR : ∀ u, 0 ≤ u → itoWordStep B j X 0 u = itoIntegral_process B k X 0 u := by
    intro u hu; funext ω; simp [itoWordStep, itoWordIntegral_cons_long, hu, hj, k]
  refine levelBound_contVersion B hT (fun u => measurable_itoWordStep B j X hX.meas_all 0 u)
    hadapt (fun q hq => div_nonneg (mul_nonneg (itoEvenConst_nonneg hq) (hX.A_nonneg q hq))
      (by positivity))
    (fun q hq => mul_nonneg (itoEvenConst_nonneg hq) (mul_nonneg (hX.A_nonneg q hq) (pow_nonneg hT e)))
    (fun q hq u hu huT => ?_) (fun q hq u hu huT => ?_) (fun q hq => ?_)
  · obtain ⟨L, hH⟩ := hX.holderAdaptedEven hq
    rw [hR u hu]
    exact (nrm_itoIntegral_process_le B k hq hH (hX.A_nonneg q hq) (hX.mom q hq) hu huT).1
  · obtain ⟨L, hH⟩ := hX.holderAdaptedEven hq
    rw [hR u hu]
    calc _ ≤ itoEvenConst q * (A q * (u ^ (e + 1) / (e + 1))) :=
          (nrm_itoIntegral_process_le B k hq hH (hX.A_nonneg q hq) (hX.mom q hq) hu huT).2
      _ = _ := by ring
  · obtain ⟨L, hH⟩ := hX.holderAdaptedEven hq
    intro u v hu huv hvT
    rw [hR v (hu.trans huv), hR u hu]
    exact nrm_itoIntegral_process_sub_le B k hq hH (hX.mom_le_T hq) hu huv hvT

/-- **Time letter step.** -/
theorem levelBound_timeStep (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) {X : ℝ → Ω → ℝ}
    {e : ℕ} {A L : ℕ → ℝ} (hX : LevelBound B T X e A L) (j : Fin (d + 1)) (hj : (j : ℕ) = 0)
    (hadapt : ∀ u, 0 ≤ u → u ≤ T →
      Measurable[(pathFiltration B).σAlg u] (contVersion (itoWordStep B j X 0) u)) :
    LevelBound B T (contVersion (itoWordStep B j X 0)) (e + 2)
      (fun q => A q * nrm q (1 / ((q * e : ℕ) + 1 : ℝ))) (fun q => A q * T ^ e * T) := by
  have hR : ∀ u, 0 ≤ u → u ≤ T →
      itoWordStep B j X 0 u =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..u, X s ω := by
    intro u hu huT
    filter_upwards [hX.cont] with ω hω
    simp only [itoWordStep, itoWordIntegral_cons_long, hu, hj, ↓reduceIte, ↓reduceDIte]
    exact lebIntegral_process_eq_integral hu huT hω
  refine levelBound_contVersion B hT (fun u => measurable_itoWordStep B j X hX.meas_all 0 u)
    hadapt (fun q hq => mul_nonneg (hX.A_nonneg q hq) (nrm_nonneg q (by positivity)))
    (fun q hq => mul_nonneg (mul_nonneg (hX.A_nonneg q hq) (pow_nonneg hT e)) hT)
    (fun q hq u hu huT => ?_) (fun q hq u hu huT => ?_) (fun q hq => ?_)
  · exact (nrm_integral_time_le hq hX.cont (hX.memLp q hq) (hX.A_nonneg q hq) (hX.mom q hq)
      hu huT).1.ae_eq (hR u hu huT).symm
  · rw [integral_ae_congr_pow (hR u hu huT)]
    calc _ ≤ A q * u ^ (e + 2) * nrm q (1 / ((q * e : ℕ) + 1 : ℝ)) :=
          (nrm_integral_time_le hq hX.cont (hX.memLp q hq) (hX.A_nonneg q hq) (hX.mom q hq)
            hu huT).2
      _ = _ := by ring
  · have hM0 : 0 ≤ A q * T ^ e := mul_nonneg (hX.A_nonneg q hq) (pow_nonneg hT e)
    intro u v hu huv hvT
    have hv0 : 0 ≤ v := hu.trans huv
    have hd : (fun ω => itoWordStep B j X 0 v ω - itoWordStep B j X 0 u ω) =ᵐ[P]
        fun ω => ∫ s in u..v, X s ω := by
      filter_upwards [hR v hv0 hvT, hR u hu (huv.trans hvT), hX.cont] with ω h1 h2 hω
      rw [h1, h2]
      have hi : ∀ w, 0 ≤ w → w ≤ T → IntervalIntegrable (fun s => X s ω) volume 0 w :=
        fun w hw hwT => (hω.mono (by rw [uIcc_of_le hw]; exact Icc_subset_Icc le_rfl hwT)
          ).intervalIntegrable
      exact intervalIntegral.integral_interval_sub_left (hi v hv0 hvT) (hi u hu (huv.trans hvT))
    rw [integral_ae_congr_pow hd]
    calc _ ≤ A q * T ^ e * (v - u) ^ 2 :=
          (nrm_integral_time_sub_le hq hX.cont (hX.memLp q hq) (hX.mom_le_T hq) hu huv hvT).2
      _ ≤ A q * T ^ e * T * (v - u) := by
          have h1 : (v - u) * (v - u) ≤ T * (v - u) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          have := mul_le_mul_of_nonneg_left h1 hM0
          nlinarith

/-- **Level one**: the time letter (`u`) and a Brownian letter (`W_u`). -/
theorem levelBound_single (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) (j : Fin (d + 1)) :
    LevelBound B T (fun u ω => itoWordIntegral B 0 u ω [j]) (wordExp [j])
      (fun q => wordConst q [j]) (fun q => wordIncr q T [j]) := by
  have hmeas : ∀ u, 0 ≤ u → u ≤ T →
      Measurable[(pathFiltration B).σAlg u] (fun ω => itoWordIntegral B 0 u ω [j]) :=
    fun u hu _ => measurable_itoWordIntegral_pathFiltration B le_rfl hu le_rfl _
  by_cases hj : (j : ℕ) = 0
  · have hX : (fun u ω => itoWordIntegral B 0 u ω [j]) = fun u (_ : Ω) => u := by
      funext u ω; simp [itoWordIntegral, itoWordIntegral_le1, hj]
    have he : wordExp [j] = 2 := by simp [wordExp, letterExp, hj]
    have hc : (fun q => wordConst q [j]) = fun _ => (1 : ℝ) := by
      funext q; simp [wordConst, hj]
    have hi : (fun q => wordIncr q T [j]) = fun _ => T := by
      funext q; simp [wordIncr, hj]
    rw [hX, he, hc, hi]
    refine ⟨fun _ _ => zero_le_one, fun _ _ => hT, fun _ _ _ => measurable_const, fun _ => measurable_const,
      Eventually.of_forall fun ω => continuousOn_id, fun q _ u _ _ => memLp_const u,
      fun q hq u hu _ => ?_, fun q hq u v hu huv hvT => ?_⟩
    · have hq0 : q ≠ 0 := by omega
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [pow_mul, nrm_pow_self hq0 (sq_nonneg u)]
    · have hq0 : q ≠ 0 := by omega
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [pow_mul, nrm_pow_self hq0 (sq_nonneg _), sq]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · set k := spaceLetterIndex j hj
    have hX : (fun u ω => itoWordIntegral B 0 u ω [j]) = fun u ω => wnnIncr B k 0 u ω := by
      funext u ω
      simp only [itoWordIntegral, itoWordIntegral_le1, ne_eq, not_true_eq_false,
        ↓reduceIte, hj, ↓reduceDIte, wnnIncr, MultiBrownian.W_zero, Real.toNNReal_zero, B.Wnn_zero]
      rfl
    have he : wordExp [j] = 1 := by simp [wordExp, letterExp, hj]
    have hc : (fun q => wordConst q [j]) = fun q => nrm q (gaussMoment q) := by
      funext q; simp [wordConst, hj]
    have hi : (fun q => wordIncr q T [j]) = fun q => nrm q (gaussMoment q) := by
      funext q; simp [wordIncr, hj]
    have hmeas' : ∀ u, 0 ≤ u → u ≤ T →
        Measurable[(pathFiltration B).σAlg u] (fun ω => wnnIncr B k 0 u ω) := by
      intro u hu huT
      have h := hmeas u hu huT
      rwa [show (fun ω => itoWordIntegral B 0 u ω [j]) = fun ω => wnnIncr B k 0 u ω from
        congrFun hX u] at h
    rw [hX, he, hc, hi]
    refine ⟨fun q _ => nrm_nonneg q (gaussMoment_nonneg q),
      fun q _ => nrm_nonneg q (gaussMoment_nonneg q), hmeas',
      fun u => measurable_wnnIncr B k 0 u, Eventually.of_forall fun ω => ?_,
      fun q _ u hu _ => memLp_even_of_integrable_pow (measurable_wnnIncr B k 0 u).aestronglyMeasurable
        (integrable_wnnIncr_pow_even B k q le_rfl hu),
      fun q hq u hu _ => ?_, fun q hq u v hu huv hvT => ?_⟩
    · simp only [wnnIncr]
      exact (((B.pathContinuous k ω).comp continuous_real_toNNReal).sub
        continuous_const).continuousOn
    · have hq0 : q ≠ 0 := by omega
      rw [integral_wnnIncr_pow_even B k q le_rfl hu, sub_zero,
        nrm_mul q (gaussMoment_nonneg q) (pow_nonneg hu q), nrm_pow_self hq0 hu, pow_one]
    · have hq0 : q ≠ 0 := by omega
      have hd : ∀ ω, wnnIncr B k 0 v ω - wnnIncr B k 0 u ω = wnnIncr B k u v ω := by
        intro ω; simp [wnnIncr]
      simp_rw [hd]
      rw [integral_wnnIncr_pow_even B k q hu huv,
        nrm_mul q (gaussMoment_nonneg q) (pow_nonneg (sub_nonneg.2 huv) q),
        nrm_pow_self hq0 (sub_nonneg.2 huv)]

/-- **Level-wise bounds for every non-empty word** (induction on the word length). -/
theorem levelBound_itoWordIntegral (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ I : Word (d + 1), I ≠ [] →
      LevelBound B T (fun u ω => itoWordIntegral B 0 u ω I) (wordExp I)
        (fun q => wordConst q I) (fun q => wordIncr q T I)
  | [], h => absurd rfl h
  | j :: I, _ => by
    by_cases hI : I = []
    · subst hI; exact levelBound_single B hT j
    · have ih := levelBound_itoWordIntegral B hT I hI
      have hX : (fun u ω => itoWordIntegral B 0 u ω (j :: I)) =
          contVersion (itoWordStep B j (fun u ω => itoWordIntegral B 0 u ω I) 0) := by
        funext u ω; simp [itoWordIntegral, hI]
      have hadapt : ∀ u, 0 ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg u]
          (contVersion (itoWordStep B j (fun u ω => itoWordIntegral B 0 u ω I) 0) u) := by
        intro u hu _
        rw [← hX]
        exact measurable_itoWordIntegral_pathFiltration B le_rfl hu le_rfl _
      rw [hX]
      by_cases hj : (j : ℕ) = 0
      · have he : wordExp (j :: I) = wordExp I + 2 := by simp [wordExp, letterExp, hj]
        have hc : (fun q => wordConst q (j :: I)) =
            fun q => wordConst q I * nrm q (1 / ((q * wordExp I : ℕ) + 1 : ℝ)) := by
          funext q; simp [wordConst, hI, hj]
        have hi : (fun q => wordIncr q T (j :: I)) =
            fun q => wordConst q I * T ^ wordExp I * T := by
          funext q; simp [wordIncr, hI, hj]
        rw [he, hc, hi]
        exact levelBound_timeStep B hT ih j hj hadapt
      · have he : wordExp (j :: I) = wordExp I + 1 := by simp [wordExp, letterExp, hj]
        have hc : (fun q => wordConst q (j :: I)) =
            fun q => itoEvenConst q * wordConst q I / (wordExp I + 1) := by
          funext q; simp [wordConst, hI, hj]
        have hi : (fun q => wordIncr q T (j :: I)) =
            fun q => itoEvenConst q * (wordConst q I * T ^ wordExp I) := by
          funext q; simp [wordIncr, hI, hj]
        rw [he, hc, hi]
        exact levelBound_itoStep B hT ih j hj hadapt

end SignatureVolatility
