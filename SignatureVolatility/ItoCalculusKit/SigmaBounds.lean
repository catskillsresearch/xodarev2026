module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal


namespace SignatureVolatility

/-!
# Moment and increment bounds for `⟨ℓ, Ŵ⟩`

Coordinates of `Ŵ_{0,t}` are Stratonovich combinations of Itô words, so the level-wise Itô
bounds of `LevelDecay` give `L^{2q}` bounds for each coordinate and for each coordinate increment
(`eLpNorm_paperSig2_coeff_sub_le`). Summing over levels against `‖ℓ_n‖ ≤ C rⁿ` gives uniform
moments (`dualPairing_paperSig2_moment`) and Hölder-`1/2` increments
(`dualPairing_paperSig2_incr`) of `σ_t = ⟨ℓ, Ŵ_t⟩`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Stratonovich combinations -/

lemma stratItoCorrection_eq_sum' (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω)
    (K : Word (d + 1)) :
    stratItoCorrection B 0 t ω K = ∑ m ∈ Finset.range K.length,
      ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff K J * itoWordIntegral B 0 t ω J := by
  by_cases hK : 2 ≤ K.length
  · exact stratItoCorrection_eq_sum B t ω hK
  rw [stratItoCorrection_of_length_le_one B 0 t ω K (by omega)]
  symm
  refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun J hJ => ?_
  by_cases ha : stratItoCoeff K J = 0
  · simp [ha]
  have h2 := length_le_two_mul_of_stratItoCoeff_ne_zero ha
  have hJm : J.length = m := wordsOfLength.mem.1 hJ
  have := Finset.mem_range.1 hm
  omega

lemma paperSig2_coeff_eq_sum (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) (I : Word (d + 1)) :
    (paperSig2 B 0 t ω).coeff I = itoWordIntegral B 0 t ω I.reverse +
      ∑ m ∈ Finset.range I.length, ∑ J ∈ wordsOfLength (d + 1) m,
        stratItoCoeff I.reverse J * itoWordIntegral B 0 t ω J := by
  simp only [paperSig2_coeff, stratWordIntegral, stratItoCorrection_eq_sum', List.length_reverse]

omit [IsProbabilityMeasure P] in
/-- `L^{2q}` bound for the correction sum of a Stratonovich combination. -/
theorem eLpNorm_stratSum_le {q : ℕ} (hq : 2 ≤ q) (g : Word (d + 1) → Ω → ℝ)
    (K : Word (d + 1)) {β : ℝ} (hβ : 0 ≤ β)
    (hg : ∀ J : Word (d + 1), J ≠ [] → J.length < K.length → K.length ≤ 2 * J.length →
      eLpNorm (g J) (2 * q : ℕ) P ≤ ENNReal.ofReal β) :
    eLpNorm (fun ω => ∑ m ∈ Finset.range K.length, ∑ J ∈ wordsOfLength (d + 1) m,
      stratItoCoeff K J * g J ω) (2 * q : ℕ) P ≤
      ENNReal.ofReal (K.length * ((d : ℝ) + 1) ^ K.length * 2 ^ K.length * β) := by
  have h1q : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  set n := K.length
  set c : ℝ := 2 ^ n * β
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) hβ
  have hfun : (fun ω => ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
      stratItoCoeff K J * g J ω) = ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
        fun ω => stratItoCoeff K J * g J ω := by
    funext ω; simp [Finset.sum_apply]
  have hterm : ∀ m ∈ Finset.range n, ∀ J ∈ wordsOfLength (d + 1) m,
      eLpNorm (fun ω => stratItoCoeff K J * g J ω) (2 * q : ℕ) P ≤ ENNReal.ofReal c := by
    intro m hm J hJ
    have hJm : J.length = m := wordsOfLength.mem.1 hJ
    have hm' : m < n := Finset.mem_range.1 hm
    by_cases ha : stratItoCoeff K J = 0
    · simp [ha]
    have h2 := length_le_two_mul_of_stratItoCoeff_ne_zero ha
    have hJne : J ≠ [] := by
      rintro rfl; rw [List.length_nil] at h2; omega
    have e : (fun ω => stratItoCoeff K J * g J ω) = stratItoCoeff K J • g J := by
      funext ω; simp
    rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (stratItoCoeff_nonneg K J)]
    have hA : ENNReal.ofReal (stratItoCoeff K J) ≤ ENNReal.ofReal (2 ^ n) :=
      ENNReal.ofReal_le_ofReal (stratItoCoeff_le K J)
    calc ENNReal.ofReal (stratItoCoeff K J) * eLpNorm (g J) (2 * q : ℕ) P
          ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal β :=
          mul_le_mul' hA (hg J hJne (by omega) h2)
      _ = ENNReal.ofReal c := (ENNReal.ofReal_mul (by positivity)).symm
  rw [hfun]
  calc eLpNorm (∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
        fun ω => stratItoCoeff K J * g J ω) (2 * q : ℕ) P
      ≤ ∑ m ∈ Finset.range n, eLpNorm (∑ J ∈ wordsOfLength (d + 1) m,
        fun ω => stratItoCoeff K J * g J ω) (2 * q : ℕ) P := eLpNorm_sum_le h1q
    _ ≤ ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
        eLpNorm (fun ω => stratItoCoeff K J * g J ω) (2 * q : ℕ) P :=
        Finset.sum_le_sum fun m _ => eLpNorm_sum_le h1q
    _ ≤ ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m, ENNReal.ofReal c :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun J hJ => hterm m hm J hJ
    _ = ENNReal.ofReal (∑ m ∈ Finset.range n, ((wordsOfLength (d + 1) m).card : ℝ) * c) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (wordsOfLength (d + 1) m).card),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (n * ((d : ℝ) + 1) ^ n * 2 ^ n * β) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑ m ∈ Finset.range n, ((wordsOfLength (d + 1) m).card : ℝ) * c
            ≤ ∑ _m ∈ Finset.range n, ((d : ℝ) + 1) ^ n * c := by
              apply Finset.sum_le_sum
              intro m hm
              rw [card_wordsOfLength]
              push_cast
              exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith)
                (Finset.mem_range.1 hm).le) hc0
          _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, c]; ring

omit [IsProbabilityMeasure P] in
/-- `L^{2q}` bound for a full Stratonovich combination `g(Iʳ) + Σ a_{Iʳ,J} g(J)`. -/
theorem eLpNorm_stratComb_le {q : ℕ} (hq : 2 ≤ q) (g : Word (d + 1) → Ω → ℝ)
    (I : Word (d + 1)) {β : ℝ} (hβ : 0 ≤ β)
    (hg : ∀ J : Word (d + 1), J ≠ [] → J.length ≤ I.length → I.length ≤ 2 * J.length →
      eLpNorm (g J) (2 * q : ℕ) P ≤ ENNReal.ofReal β) (hI : I ≠ []) :
    eLpNorm (fun ω => g I.reverse ω + ∑ m ∈ Finset.range I.length,
      ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff I.reverse J * g J ω) (2 * q : ℕ) P ≤
      ENNReal.ofReal ((1 + I.length * ((d : ℝ) + 1) ^ I.length * 2 ^ I.length) * β) := by
  have h1q : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hK : I.reverse ≠ [] := by simpa using hI
  have h1 := hg I.reverse hK (by simp) (by simp; omega)
  have h2 := eLpNorm_stratSum_le (P := P) hq g I.reverse hβ
    (fun J hJ hl h2 => hg J hJ (by simp at hl; omega) (by simpa using h2))
  rw [List.length_reverse] at h2
  have e : (fun ω => g I.reverse ω + ∑ m ∈ Finset.range I.length,
      ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff I.reverse J * g J ω) =
      g I.reverse + fun ω => ∑ m ∈ Finset.range I.length,
        ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff I.reverse J * g J ω := rfl
  rw [e]
  refine (eLpNorm_add_le h1q).trans ?_
  calc _ ≤ ENNReal.ofReal β +
        ENNReal.ofReal (I.length * ((d : ℝ) + 1) ^ I.length * 2 ^ I.length * β) :=
        add_le_add h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_add hβ (by positivity)]
        congr 1; ring

/-! ## Increments of the coordinates -/

lemma momBound_mono (q : ℕ) {s t : ℝ} (hst : s ≤ t) (n : ℕ) : momBound q s n ≤ momBound q t n := by
  unfold momBound
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by linarith [one_le_decayConst_mul q s])
  apply mul_le_mul_of_nonneg_left _ (by linarith [one_le_decayConst q])
  exact pow_le_pow_left₀ (by linarith [le_max_left 1 s]) (max_le_max le_rfl hst) 2

lemma eLpNorm_itoWordIntegral_sub_le_momBound (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q)
    {T : ℝ} (hT : 0 ≤ T) {J : Word (d + 1)} (hJ : J ≠ []) {n : ℕ} (h1 : n ≤ 2 * J.length)
    (h2 : J.length ≤ n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    eLpNorm (fun ω => itoWordIntegral B 0 v ω J - itoWordIntegral B 0 u ω J) (2 * q : ℕ) P ≤
      ENNReal.ofReal (n * momBound q T n * Real.sqrt (v - u)) := by
  refine (eLpNorm_itoWordIntegral_sub_le B hq hT J hJ hu huv hvT).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hW0 : 0 ≤ wordIncr q T J := (levelBound_itoWordIntegral (P := P) B hT J hJ).L_nonneg q hq
  rw [Real.sqrt_mul hW0]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hM0 := momBound_nonneg q T n
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ n * momBound q T n)]
  apply Real.sqrt_le_sqrt
  set m := J.length
  have hm1 : 1 ≤ m := List.length_pos_iff.2 hJ
  set D := decayConst q * max 1 T ^ 2
  have hD : 1 ≤ D := one_le_decayConst_mul q T
  set z : ℝ := (1 : ℝ) / ((n / 2).factorial : ℝ)
  have hz : 0 ≤ z := by positivity
  have hsq : momBound q T n ^ 2 = D ^ (2 * n) * nrm q z := by
    simp only [momBound]
    rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (z ^ _), ← Real.rpow_mul hz, nrm]
    congr 2
    · ring
    · push_cast; field_simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hfac : (1 : ℝ) / ((m - 1).factorial : ℝ) ≤ n * z := by
    have hnat : (n / 2).factorial ≤ n * (m - 1).factorial := by
      calc (n / 2).factorial ≤ m.factorial := Nat.factorial_le (by omega)
        _ = m * (m - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
        _ ≤ n * (m - 1).factorial := Nat.mul_le_mul_right _ h2
    have hnr : ((n / 2).factorial : ℝ) ≤ n * ((m - 1).factorial : ℝ) := by exact_mod_cast hnat
    have hp1 : (0 : ℝ) < ((m - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hp2 : (0 : ℝ) < ((n / 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp only [z]
    rw [mul_one_div, div_le_div_iff₀ hp1 hp2]
    linarith
  have hnq : nrm q (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    unfold nrm
    have hq1 : 1 / (q : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    calc (n : ℝ) ^ (1 / (q : ℝ)) ≤ (n : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 hq1
      _ = (n : ℝ) ^ 2 := Real.rpow_two _
  have hnrm : nrm q (1 / ((m - 1).factorial : ℝ)) ≤ (n : ℝ) ^ 2 * nrm q z :=
    calc nrm q (1 / ((m - 1).factorial : ℝ)) ≤ nrm q (n * z) := nrm_mono (by positivity) hfac
      _ = nrm q n * nrm q z := nrm_mul q (by positivity) hz
      _ ≤ (n : ℝ) ^ 2 * nrm q z := mul_le_mul_of_nonneg_right hnq (nrm_nonneg q hz)
  calc wordIncr q T J ≤ decayConst q ^ m * max 1 T ^ (2 * m) *
        nrm q (1 / ((m - 1).factorial : ℝ)) := wordIncr_le hq hT J hJ
    _ = D ^ m * nrm q (1 / ((m - 1).factorial : ℝ)) := by
        simp only [D]; rw [mul_pow, ← pow_mul]
    _ ≤ D ^ (2 * n) * ((n : ℝ) ^ 2 * nrm q z) :=
        mul_le_mul (pow_le_pow_right₀ hD (by omega)) hnrm (nrm_nonneg q (by positivity))
          (by positivity)
    _ = _ := by
        rw [show ((n : ℝ) * momBound q T n) ^ 2 = (n : ℝ) ^ 2 * momBound q T n ^ 2 from
          mul_pow _ _ _, hsq]; ring

/-- `L^{2q}` increment bound for one coordinate of `Ŵ_{0,·}` on `[0, T]`. -/
theorem eLpNorm_paperSig2_coeff_sub_le (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q) {T : ℝ}
    (hT : 0 ≤ T) (I : Word (d + 1)) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    eLpNorm (fun ω => (paperSig2 B 0 v ω).coeff I - (paperSig2 B 0 u ω).coeff I) (2 * q : ℕ) P ≤
      ENNReal.ofReal ((1 + I.length * ((d : ℝ) + 1) ^ I.length * 2 ^ I.length) *
        (I.length * momBound q T I.length * Real.sqrt (v - u))) := by
  by_cases hI : I = []
  · subst hI; simp [paperSig2_empty]
  set g : Word (d + 1) → Ω → ℝ :=
    fun J ω => itoWordIntegral B 0 v ω J - itoWordIntegral B 0 u ω J
  have e : (fun ω => (paperSig2 B 0 v ω).coeff I - (paperSig2 B 0 u ω).coeff I) =
      fun ω => g I.reverse ω + ∑ m ∈ Finset.range I.length,
        ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff I.reverse J * g J ω := by
    funext ω
    simp only [paperSig2_coeff_eq_sum, g, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e]
  exact eLpNorm_stratComb_le hq g I (by have := momBound_nonneg q T I.length; positivity)
    (fun J hJ h1 h2 => eLpNorm_itoWordIntegral_sub_le_momBound B hq hT hJ h2 h1 hu huv hvT) hI

/-! ## Level sums -/

lemma abs_coeff_le_levelNorm {D : ℕ} (ℓ : ExtTensorAlgebra D) {n : ℕ} {I : Word D}
    (hI : I ∈ wordsOfLength D n) : |ℓ.coeff I| ≤ ℓ.levelNorm n := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun J => ℓ.coeff J ^ 2) (fun J _ => sq_nonneg _) hI

lemma abs_levelInner_sub_le {D : ℕ} (ℓ a b : ExtTensorAlgebra D) (n : ℕ) :
    |ℓ.levelInner a n - ℓ.levelInner b n| ≤
      ℓ.levelNorm n * ∑ I ∈ wordsOfLength D n, |a.coeff I - b.coeff I| := by
  simp only [ExtTensorAlgebra.levelInner, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_coeff_le_levelNorm ℓ hI) (abs_nonneg _)

lemma abs_levelInner_le {D : ℕ} (ℓ a : ExtTensorAlgebra D) (n : ℕ) :
    |ℓ.levelInner a n| ≤ ℓ.levelNorm n * ∑ I ∈ wordsOfLength D n, |a.coeff I| := by
  simp only [ExtTensorAlgebra.levelInner, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_coeff_le_levelNorm ℓ hI) (abs_nonneg _)

omit [IsProbabilityMeasure P] in
/-- `L^{2q}` bound for a weighted level sum `a · Σ_{|I| = n} |f_I|`. -/
lemma eLpNorm_levelSum_le {q : ℕ} (hq : 1 ≤ q) (f : Word (d + 1) → Ω → ℝ)
    (hf : ∀ I, Measurable (f I)) (n : ℕ) {a β : ℝ} (ha : 0 ≤ a)
    (hb : ∀ I ∈ wordsOfLength (d + 1) n, eLpNorm (f I) (2 * q : ℕ) P ≤ ENNReal.ofReal β) :
    eLpNorm (fun ω => a * ∑ I ∈ wordsOfLength (d + 1) n, |f I ω|) (2 * q : ℕ) P ≤
      ENNReal.ofReal (a * (((d : ℝ) + 1) ^ n * β)) := by
  have h1q : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  have e : (fun ω => a * ∑ I ∈ wordsOfLength (d + 1) n, |f I ω|) =
      a • ∑ I ∈ wordsOfLength (d + 1) n, fun ω => ‖f I ω‖ := by
    funext ω; simp [Finset.sum_apply, Real.norm_eq_abs]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal ha]
  have hsum : eLpNorm (∑ I ∈ wordsOfLength (d + 1) n, fun ω => ‖f I ω‖) (2 * q : ℕ) P ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ n * β) := by
    refine (eLpNorm_sum_le h1q).trans ?_
    calc ∑ I ∈ wordsOfLength (d + 1) n, eLpNorm (fun ω => ‖f I ω‖) (2 * q : ℕ) P
        ≤ ∑ _I ∈ wordsOfLength (d + 1) n, ENNReal.ofReal β := by
          refine Finset.sum_le_sum fun I hI => ?_
          rw [eLpNorm_norm _ (hf I).aestronglyMeasurable]
          exact hb I hI
      _ = ENNReal.ofReal (((d : ℝ) + 1) ^ n * β) := by
          have hcard : ((wordsOfLength (d + 1) n).card : ℝ) = ((d : ℝ) + 1) ^ n := by
            rw [card_wordsOfLength]; push_cast; rfl
          rw [Finset.sum_const, nsmul_eq_mul, ← hcard,
            ENNReal.ofReal_mul (Nat.cast_nonneg (wordsOfLength (d + 1) n).card),
            ENNReal.ofReal_natCast]
  calc ENNReal.ofReal a * eLpNorm (∑ I ∈ wordsOfLength (d + 1) n, fun ω => ‖f I ω‖)
        (2 * q : ℕ) P ≤ ENNReal.ofReal a * ENNReal.ofReal (((d : ℝ) + 1) ^ n * β) :=
        mul_le_mul' le_rfl hsum
    _ = _ := (ENNReal.ofReal_mul ha).symm

/-- **Summation of dominated series in `L^{2q}`.** -/
theorem memLp_integral_tsum_pow_le {Z Y : ℕ → Ω → ℝ} (hZm : ∀ n, Measurable (Z n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hYm : ∀ n, Measurable (Y n)) (hZY : ∀ n ω, |Z n ω| ≤ Y n ω)
    {q : ℕ} (hq : 1 ≤ q) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, eLpNorm (Y n) (2 * q : ℕ) P ≤ ENNReal.ofReal (b n)) (hbs : Summable b) :
    (∀ᵐ ω ∂P, Summable fun n => Z n ω) ∧ MemLp (fun ω => ∑' n, Z n ω) (2 * q : ℕ) P ∧
      ∫ ω, (∑' n, Z n ω) ^ (2 * q) ∂P ≤ (∑' n, b n) ^ (2 * q) := by
  have hN : 1 ≤ 2 * q := by omega
  have hev : Even (2 * q) := ⟨q, by ring⟩
  obtain ⟨hsum, hint⟩ := summable_integrable_of_eLpNorm_le hY0 hYm hN hb0 hb hbs
    (p := ((2 * q : ℕ) : ℝ)) (by exact_mod_cast hN) le_rfl
  have hint' : Integrable (fun ω => (∑' n, Y n ω) ^ (2 * q)) P := by
    refine hint.congr (Eventually.of_forall fun ω => ?_)
    simp only [Real.rpow_natCast]
  have hZs : ∀ᵐ ω ∂P, Summable fun n => Z n ω := by
    filter_upwards [hsum] with ω hω
    exact Summable.of_norm_bounded hω fun n => by rw [Real.norm_eq_abs]; exact hZY n ω
  have hdom : ∀ᵐ ω ∂P, (∑' n, Z n ω) ^ (2 * q) ≤ (∑' n, Y n ω) ^ (2 * q) := by
    filter_upwards [hsum, hZs] with ω hω hz
    have habs : |∑' n, Z n ω| ≤ ∑' n, Y n ω := by
      calc |∑' n, Z n ω| = ‖∑' n, Z n ω‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' n, ‖Z n ω‖ := norm_tsum_le_tsum_norm hz.norm
        _ ≤ ∑' n, Y n ω := hz.norm.tsum_le_tsum
            (fun n => by rw [Real.norm_eq_abs]; exact hZY n ω) hω
    rw [← hev.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs _
  have hZm' : Measurable fun ω => ∑' n, Z n ω := Measurable.tsum hZm
  have hint2 : Integrable (fun ω => (∑' n, Z n ω) ^ (2 * q)) P :=
    hint'.mono' (hZm'.pow_const _).aestronglyMeasurable (hdom.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hev.pow_nonneg _)]; exact h)
  refine ⟨hZs, memLp_even_of_integrable_pow hZm'.aestronglyMeasurable hint2, ?_⟩
  calc ∫ ω, (∑' n, Z n ω) ^ (2 * q) ∂P ≤ ∫ ω, (∑' n, Y n ω) ^ (2 * q) ∂P :=
        integral_mono_ae hint2 hint' hdom
    _ ≤ _ := integral_tsum_pow_le hY0 hYm hN hb0 hb hbs

/-- The level weights `Rⁿ (d+1)ⁿ (1 + n (d+1)ⁿ 2ⁿ) (n+1) M_q(t, n)` are summable. -/
lemma summable_levelWeight (q : ℕ) (hq : 2 ≤ q) (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ => R ^ n * (((d : ℝ) + 1) ^ n *
      ((1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * ((n + 1) * momBound q t n))) := by
  have h1 := summable_mul_momBound q hq t (K := 2 * (R * ((d : ℝ) + 1))) (by positivity)
  have h2 := summable_mul_momBound q hq t (K := 4 * (R * ((d : ℝ) + 1) ^ 2 * 2))
    (by positivity)
  refine Summable.of_nonneg_of_le (fun n => by have := momBound_nonneg q t n; positivity)
    (fun n => ?_) (h1.add h2)
  have hM := momBound_nonneg q t n
  have hn2 : (n : ℝ) + 1 ≤ 2 ^ n := by
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast this
  have hn2' : (n : ℝ) ≤ 2 ^ n := by linarith
  have hnn : (n : ℝ) * ((n : ℝ) + 1) ≤ 4 ^ n := by
    calc (n : ℝ) * ((n : ℝ) + 1) ≤ 2 ^ n * 2 ^ n :=
          mul_le_mul hn2' hn2 (by positivity) (by positivity)
      _ = 4 ^ n := by rw [← mul_pow]; norm_num
  have hA0 : 0 ≤ (R * ((d : ℝ) + 1)) ^ n * momBound q t n := by positivity
  have hB0 : 0 ≤ (R * ((d : ℝ) + 1) ^ 2 * 2) ^ n * momBound q t n := by positivity
  calc R ^ n * (((d : ℝ) + 1) ^ n * ((1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) *
        ((n + 1) * momBound q t n)))
      = ((n : ℝ) + 1) * ((R * ((d : ℝ) + 1)) ^ n * momBound q t n) +
        ((n : ℝ) * ((n : ℝ) + 1)) * ((R * ((d : ℝ) + 1) ^ 2 * 2) ^ n * momBound q t n) := by
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
    _ ≤ 2 ^ n * ((R * ((d : ℝ) + 1)) ^ n * momBound q t n) +
        4 ^ n * ((R * ((d : ℝ) + 1) ^ 2 * 2) ^ n * momBound q t n) :=
        add_le_add (mul_le_mul_of_nonneg_right hn2 hA0) (mul_le_mul_of_nonneg_right hnn hB0)
    _ = _ := by rw [mul_pow (2 : ℝ), mul_pow (4 : ℝ)]; ring

/-! ## Moments and increments of `σ_t = ⟨ℓ, Ŵ_t⟩` -/

lemma measurable_levelInner_paperSig2 (B : MultiBrownian Ω P d) (ℓ : ExtTensorAlgebra (d + 1))
    (t : ℝ) (n : ℕ) : Measurable fun ω => ℓ.levelInner (paperSig2 B 0 t ω) n :=
  Finset.measurable_sum _ fun I _ => (measurable_paperSig2_coeff B 0 t I).const_mul _

/-- **Uniform `L^{2q}` moments** of `⟨ℓ, Ŵ_s⟩` on `[0, t]` when `‖ℓ_n‖ ≤ C rⁿ`. -/
theorem dualPairing_paperSig2_moment (B : MultiBrownian Ω P d) {ℓ : ExtTensorAlgebra (d + 1)}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) {q : ℕ}
    (hq : 2 ≤ q) {t : ℝ} :
    ∃ M, 0 ≤ M ∧ ∀ s, 0 ≤ s → s ≤ t →
      (∀ᵐ ω ∂P, Summable fun n => ℓ.levelInner (paperSig2 B 0 s ω) n) ∧
      MemLp (fun ω => dualPairing ℓ (paperSig2 B 0 s ω)) (2 * q : ℕ) P ∧
      ∫ ω, dualPairing ℓ (paperSig2 B 0 s ω) ^ (2 * q) ∂P ≤ M := by
  set b : ℕ → ℝ := fun n => C * (r ^ n * (((d : ℝ) + 1) ^ n *
    ((1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * ((n + 1) * momBound q t n))))
  have hb0 : ∀ n, 0 ≤ b n := fun n => by have := momBound_nonneg q t n; positivity
  have hbs : Summable b := (summable_levelWeight q hq t hr).mul_left C
  refine ⟨(∑' n, b n) ^ (2 * q), pow_nonneg (tsum_nonneg hb0) _, fun s hs hst => ?_⟩
  set Y : ℕ → Ω → ℝ := fun n ω =>
    (C * r ^ n) * ∑ I ∈ wordsOfLength (d + 1) n, |(paperSig2 B 0 s ω).coeff I|
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun I _ => abs_nonneg _)
  have hYm : ∀ n, Measurable (Y n) := fun n => measurable_const.mul
    (Finset.measurable_sum _ fun I _ => (measurable_paperSig2_coeff B 0 s I).abs)
  have hZY : ∀ n ω, |ℓ.levelInner (paperSig2 B 0 s ω) n| ≤ Y n ω := fun n ω =>
    (abs_levelInner_le ℓ _ n).trans (mul_le_mul_of_nonneg_right (hℓ n)
      (Finset.sum_nonneg fun I _ => abs_nonneg _))
  have hb : ∀ n, eLpNorm (Y n) (2 * q : ℕ) P ≤ ENNReal.ofReal (b n) := by
    intro n
    refine (eLpNorm_levelSum_le (β := (1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * momBound q s n)
      (by omega) (fun I ω => (paperSig2 B 0 s ω).coeff I)
      (fun I => measurable_paperSig2_coeff B 0 s I) n (by positivity)
      (fun I hI => ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
    · have := eLpNorm_paperSig2_coeff_le B hq hs I
      rwa [wordsOfLength.mem.1 hI] at this
    · have hM := momBound_mono q hst n
      have hM0 := momBound_nonneg q s n
      have h1 : momBound q s n ≤ ((n : ℝ) + 1) * momBound q t n := by nlinarith
      simp only [b]
      rw [← mul_assoc C]
      gcongr
  obtain ⟨hs1, hs2, hs3⟩ := memLp_integral_tsum_pow_le
    (fun n => measurable_levelInner_paperSig2 B ℓ s n) hY0 hYm hZY (by omega) hb0 hb hbs
  exact ⟨hs1, hs2, hs3⟩

/-- **Hölder-`1/2` increments in `L^{2q}`** of `⟨ℓ, Ŵ_s⟩` on `[0, t]` when `‖ℓ_n‖ ≤ C rⁿ`. -/
theorem dualPairing_paperSig2_incr (B : MultiBrownian Ω P d) {ℓ : ExtTensorAlgebra (d + 1)}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hℓ : ∀ n, ℓ.levelNorm n ≤ C * r ^ n) {q : ℕ}
    (hq : 2 ≤ q) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K, 0 ≤ K ∧ ∀ u v, 0 ≤ u → u ≤ v → v ≤ t →
      Integrable (fun ω => (dualPairing ℓ (paperSig2 B 0 v ω) -
        dualPairing ℓ (paperSig2 B 0 u ω)) ^ (2 * q)) P ∧
      ∫ ω, (dualPairing ℓ (paperSig2 B 0 v ω) - dualPairing ℓ (paperSig2 B 0 u ω)) ^ (2 * q) ∂P ≤
        K * (v - u) ^ q := by
  set c : ℕ → ℝ := fun n => C * (r ^ n * (((d : ℝ) + 1) ^ n *
    ((1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * ((n + 1) * momBound q t n))))
  have hc0 : ∀ n, 0 ≤ c n := fun n => by have := momBound_nonneg q t n; positivity
  have hcs : Summable c := (summable_levelWeight q hq t hr).mul_left C
  obtain ⟨M, -, hM⟩ := dualPairing_paperSig2_moment (P := P) B hC hr hℓ hq (t := t)
  refine ⟨(∑' n, c n) ^ (2 * q), pow_nonneg (tsum_nonneg hc0) _,
    fun u v hu huv hvt => ?_⟩
  set δ := Real.sqrt (v - u)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  set b : ℕ → ℝ := fun n => c n * δ
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg (hc0 n) hδ
  have hbs : Summable b := hcs.mul_right δ
  set Z : ℕ → Ω → ℝ := fun n ω =>
    ℓ.levelInner (paperSig2 B 0 v ω) n - ℓ.levelInner (paperSig2 B 0 u ω) n
  set Y : ℕ → Ω → ℝ := fun n ω => (C * r ^ n) * ∑ I ∈ wordsOfLength (d + 1) n,
    |(paperSig2 B 0 v ω).coeff I - (paperSig2 B 0 u ω).coeff I|
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun I _ => abs_nonneg _)
  have hYm : ∀ n, Measurable (Y n) := fun n => measurable_const.mul
    (Finset.measurable_sum _ fun I _ =>
      ((measurable_paperSig2_coeff B 0 v I).sub (measurable_paperSig2_coeff B 0 u I)).abs)
  have hZY : ∀ n ω, |Z n ω| ≤ Y n ω := fun n ω =>
    (abs_levelInner_sub_le ℓ _ _ n).trans (mul_le_mul_of_nonneg_right (hℓ n)
      (Finset.sum_nonneg fun I _ => abs_nonneg _))
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    (measurable_levelInner_paperSig2 B ℓ v n).sub (measurable_levelInner_paperSig2 B ℓ u n)
  have hb : ∀ n, eLpNorm (Y n) (2 * q : ℕ) P ≤ ENNReal.ofReal (b n) := by
    intro n
    refine (eLpNorm_levelSum_le
      (β := (1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * (n * momBound q t n * δ)) (by omega)
      (fun I ω => (paperSig2 B 0 v ω).coeff I - (paperSig2 B 0 u ω).coeff I)
      (fun I => (measurable_paperSig2_coeff B 0 v I).sub (measurable_paperSig2_coeff B 0 u I))
      n (by positivity) (fun I hI => ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
    · have := eLpNorm_paperSig2_coeff_sub_le B hq ht I hu huv hvt
      rwa [wordsOfLength.mem.1 hI] at this
    · have hM0 := momBound_nonneg q t n
      have h1 : (n : ℝ) * momBound q t n ≤ ((n : ℝ) + 1) * momBound q t n := by nlinarith
      set A : ℝ := 1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n
      have hA : 0 ≤ A := by positivity
      have h2 : (n : ℝ) * momBound q t n * δ ≤ ((n : ℝ) + 1) * momBound q t n * δ :=
        mul_le_mul_of_nonneg_right h1 hδ
      have key : A * (n * momBound q t n * δ) ≤ A * ((n + 1) * momBound q t n) * δ := by
        calc A * (n * momBound q t n * δ) ≤ A * ((n + 1) * momBound q t n * δ) :=
              mul_le_mul_of_nonneg_left h2 hA
          _ = _ := by ring
      calc C * r ^ n * (((d : ℝ) + 1) ^ n * (A * (n * momBound q t n * δ)))
          ≤ C * r ^ n * (((d : ℝ) + 1) ^ n * (A * ((n + 1) * momBound q t n) * δ)) := by
            gcongr
        _ = b n := by simp only [b, c, A]; ring
  obtain ⟨-, hL, hI⟩ := memLp_integral_tsum_pow_le hZm hY0 hYm hZY (by omega) hb0 hb hbs
  obtain ⟨hsv, -, -⟩ := hM v (hu.trans huv) hvt
  obtain ⟨hsu, -, -⟩ := hM u hu (huv.trans hvt)
  have hae : (fun ω => dualPairing ℓ (paperSig2 B 0 v ω) - dualPairing ℓ (paperSig2 B 0 u ω))
      =ᵐ[P] fun ω => ∑' n, Z n ω := by
    filter_upwards [hsv, hsu] with ω h1 h2
    simp only [dualPairing, Z]
    exact (h1.tsum_sub h2).symm
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hpow : (fun ω => (dualPairing ℓ (paperSig2 B 0 v ω) -
      dualPairing ℓ (paperSig2 B 0 u ω)) ^ (2 * q)) =ᵐ[P] fun ω => (∑' n, Z n ω) ^ (2 * q) :=
    hae.mono fun ω h => by simp only [h]
  refine ⟨(integrable_pow_of_memLp_evenDeg hev hL).congr hpow.symm, ?_⟩
  rw [integral_congr_ae hpow]
  refine hI.trans (le_of_eq ?_)
  simp only [b]
  rw [tsum_mul_right, mul_pow, pow_mul δ, Real.sq_sqrt (sub_nonneg.2 huv)]

/-! ## Helpers for the continuity argument -/

lemma levelNorm_le_sum_abs {D : ℕ} (a : ExtTensorAlgebra D) (n : ℕ) :
    a.levelNorm n ≤ ∑ I ∈ wordsOfLength D n, |a.coeff I| := by
  simp only [ExtTensorAlgebra.levelNorm, ExtTensorAlgebra.levelNormSq]
  rw [← Real.sqrt_sq (Finset.sum_nonneg fun I _ => abs_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ I ∈ wordsOfLength D n, a.coeff I ^ 2 = ∑ I ∈ wordsOfLength D n, |a.coeff I| ^ 2 := by
        simp [sq_abs]
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun I _ => abs_nonneg _

omit [IsProbabilityMeasure P] in
/-- From an `L^{2q}` norm bound to a `2q`-th moment bound. -/
lemma integral_pow_le_of_eLpNorm_le {f : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hm : MemLp f (2 * q : ℕ) P) {a : ℝ} (ha : 0 ≤ a)
    (hb : eLpNorm f (2 * q : ℕ) P ≤ ENNReal.ofReal a) :
    ∫ ω, f ω ^ (2 * q) ∂P ≤ a ^ (2 * q) := by
  have h2q : ((2 * q : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show 2 * q ≠ 0 by omega)
  rw [hm.eLpNorm_eq_integral_rpow_norm h2q (ENNReal.natCast_ne_top _),
    ENNReal.toReal_natCast] at hb
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hI : ∫ ω, ‖f ω‖ ^ (((2 * q : ℕ) : ℝ)) ∂P = ∫ ω, f ω ^ (2 * q) ∂P := by
    congr 1; funext ω
    rw [Real.rpow_natCast, Real.norm_eq_abs, hev.pow_abs]
  rw [hI] at hb
  have h0 : 0 ≤ ∫ ω, f ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
  have h1 := (ENNReal.ofReal_le_ofReal_iff ha).1 hb
  have hpos : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * q by omega)
  calc ∫ ω, f ω ^ (2 * q) ∂P
      = ((∫ ω, f ω ^ (2 * q) ∂P) ^ (((2 * q : ℕ) : ℝ))⁻¹) ^ (2 * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0, inv_mul_cancel₀ hpos.ne', Real.rpow_one]
    _ ≤ a ^ (2 * q) := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) h1 _

end SignatureVolatility
