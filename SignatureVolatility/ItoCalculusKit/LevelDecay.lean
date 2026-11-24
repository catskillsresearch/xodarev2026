module

public import SignatureVolatility.ItoCalculusKit.LevelBounds

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace SignatureVolatility

/-!
# Factorial decay of the level-wise Itô bounds

`wordConst q I ≤ C_q ^ |I| · (1 / |I|!)^{1/q}` (`wordConst_le`), so the `L^{2q}` norm of every
Itô word coordinate of length `m` is at most `√(C_q^m · max(1,t)^{2m} · (1/m!)^{1/q})`
(`eLpNorm_itoWordIntegral_le`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma one_le_letterExp (j : Fin (d + 1)) : 1 ≤ letterExp j := by
  unfold letterExp; split_ifs <;> norm_num

lemma letterExp_le_two (j : Fin (d + 1)) : letterExp j ≤ 2 := by
  unfold letterExp; split_ifs <;> norm_num

lemma length_le_wordExp : ∀ I : Word (d + 1), I.length ≤ wordExp I
  | [] => le_rfl
  | j :: I => by
    have := length_le_wordExp I
    have := one_le_letterExp j
    simp only [List.length_cons, wordExp]; omega

lemma wordExp_le_two_mul_length : ∀ I : Word (d + 1), wordExp I ≤ 2 * I.length
  | [] => le_rfl
  | j :: I => by
    have := wordExp_le_two_mul_length I
    have := letterExp_le_two j
    simp only [List.length_cons, wordExp]; omega

/-- Uniform per-letter constant. -/
def decayConst (q : ℕ) : ℝ := max 1 (max (itoEvenConst q) (nrm q (gaussMoment q)))

lemma one_le_decayConst (q : ℕ) : 1 ≤ decayConst q := le_max_left _ _

lemma wordConst_nonneg {q : ℕ} (hq : 2 ≤ q) : ∀ I : Word (d + 1), 0 ≤ wordConst q I
  | [] => zero_le_one
  | j :: I => by
    have ih := wordConst_nonneg hq I
    unfold wordConst
    split_ifs
    · exact zero_le_one
    · exact nrm_nonneg q (gaussMoment_nonneg q)
    · exact mul_nonneg ih (nrm_nonneg q (by positivity))
    · exact div_nonneg (mul_nonneg (itoEvenConst_nonneg hq) ih) (by positivity)

lemma self_le_nrm {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ nrm q x := by
  rcases hx0.eq_or_lt with rfl | hx
  · exact le_of_eq (nrm_zero q (by omega)).symm
  · unfold nrm
    have : (1 / (q : ℝ)) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hq)]; exact_mod_cast hq
    simpa using Real.rpow_le_rpow_of_exponent_ge hx hx1 this

lemma nrm_one (q : ℕ) : nrm q 1 = 1 := by unfold nrm; exact Real.one_rpow _

/-- **Factorial decay** of the level constants. -/
theorem wordConst_le {q : ℕ} (hq : 2 ≤ q) : ∀ I : Word (d + 1), I ≠ [] →
    wordConst q I ≤ decayConst q ^ I.length * nrm q (1 / (I.length.factorial : ℝ))
  | [], h => absurd rfl h
  | j :: I, _ => by
    have hC := one_le_decayConst q
    by_cases hI : I = []
    · subst hI
      simp only [wordConst, ↓reduceIte, List.length_cons, List.length_nil, zero_add, pow_one,
        Nat.factorial_one, Nat.cast_one, div_one, nrm_one, mul_one]
      split_ifs
      · exact hC
      · exact (le_max_right _ _).trans (le_max_right _ _)
    · have ih := wordConst_le hq I hI
      set m := I.length with hm
      have hm1 : 1 ≤ m := List.length_pos_iff.2 hI
      have hme : m ≤ wordExp I := length_le_wordExp I
      have hA := wordConst_nonneg hq I
      have hfac : nrm q (1 / (m.factorial : ℝ)) * nrm q (1 / ((m : ℝ) + 1)) =
          nrm q (1 / ((m + 1).factorial : ℝ)) := by
        rw [← nrm_mul q (by positivity) (by positivity)]
        congr 1
        rw [Nat.factorial_succ]; push_cast; field_simp
      have hN0 : 0 ≤ nrm q (1 / (m.factorial : ℝ)) := nrm_nonneg q (by positivity)
      have hpow : decayConst q ^ m ≤ decayConst q ^ (m + 1) :=
        pow_le_pow_right₀ hC (Nat.le_succ m)
      simp only [wordConst, hI, ↓reduceIte, List.length_cons]
      split_ifs with hj
      · have h1 : nrm q (1 / ((q * wordExp I : ℕ) + 1 : ℝ)) ≤ nrm q (1 / ((m : ℝ) + 1)) := by
          apply nrm_mono (by positivity)
          apply one_div_le_one_div_of_le (by positivity)
          have : m ≤ q * wordExp I := hme.trans (Nat.le_mul_of_pos_left _ (by omega))
          exact_mod_cast Nat.add_le_add_right this 1
        calc wordConst q I * nrm q (1 / ((q * wordExp I : ℕ) + 1 : ℝ))
            ≤ (decayConst q ^ m * nrm q (1 / (m.factorial : ℝ))) * nrm q (1 / ((m : ℝ) + 1)) :=
              mul_le_mul ih h1 (nrm_nonneg q (by positivity)) (by positivity)
          _ = decayConst q ^ m * nrm q (1 / ((m + 1).factorial : ℝ)) := by rw [mul_assoc, hfac]
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow (nrm_nonneg q (by positivity))
      · have h1 : 1 / ((wordExp I : ℝ) + 1) ≤ nrm q (1 / ((m : ℝ) + 1)) := by
          refine le_trans ?_ (self_le_nrm (by omega) (by positivity) ?_)
          · apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right hme 1
          · rw [div_le_one (by positivity)]; linarith
        have hE : itoEvenConst q ≤ decayConst q :=
          (le_max_left _ _).trans (le_max_right _ _)
        calc itoEvenConst q * wordConst q I / ((wordExp I : ℝ) + 1)
            = itoEvenConst q * wordConst q I * (1 / ((wordExp I : ℝ) + 1)) := by ring
          _ ≤ decayConst q * (decayConst q ^ m * nrm q (1 / (m.factorial : ℝ))) *
              nrm q (1 / ((m : ℝ) + 1)) :=
              mul_le_mul (mul_le_mul hE ih hA (by linarith)) h1 (by positivity)
                (by positivity)
          _ = decayConst q ^ (m + 1) * nrm q (1 / ((m + 1).factorial : ℝ)) := by
              rw [← hfac, pow_succ]; ring

/-- `L^{2q}` bound for an Itô word coordinate of length `m`. -/
theorem eLpNorm_itoWordIntegral_le (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q) {t : ℝ}
    (ht : 0 ≤ t) (J : Word (d + 1)) (hJ : J ≠ []) :
    eLpNorm (fun ω => itoWordIntegral B 0 t ω J) (2 * q : ℕ) P ≤
      ENNReal.ofReal (Real.sqrt (decayConst q ^ J.length * max 1 t ^ (2 * J.length) *
        nrm q (1 / (J.length.factorial : ℝ)))) := by
  have hL := levelBound_itoWordIntegral (P := P) B ht J hJ
  have hm := hL.memLp q hq t ht le_rfl
  have hmom := hL.mom q hq t ht le_rfl
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have h2q : ((2 * q : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * q ≠ 0 by omega)
  rw [hm.eLpNorm_eq_integral_rpow_norm h2q (ENNReal.natCast_ne_top _)]
  apply ENNReal.ofReal_le_ofReal
  have hI : ∫ ω, ‖itoWordIntegral B 0 t ω J‖ ^ (((2 * q : ℕ) : ℝ≥0∞).toReal) ∂P =
      ∫ ω, itoWordIntegral B 0 t ω J ^ (2 * q) ∂P := by
    congr 1; funext ω
    rw [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, hev.pow_abs]
  have h0 : 0 ≤ ∫ ω, itoWordIntegral B 0 t ω J ^ (2 * q) ∂P :=
    integral_nonneg fun ω => hev.pow_nonneg _
  rw [hI, ENNReal.toReal_natCast]
  have hsq : (∫ ω, itoWordIntegral B 0 t ω J ^ (2 * q) ∂P) ^ (((2 * q : ℕ) : ℝ))⁻¹ =
      Real.sqrt (nrm q (∫ ω, itoWordIntegral B 0 t ω J ^ (2 * q) ∂P)) := by
    rw [Real.sqrt_eq_rpow, nrm, ← Real.rpow_mul h0]
    congr 1; push_cast; field_simp
  rw [hsq]
  apply Real.sqrt_le_sqrt
  set m := J.length
  have hT1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have htT : t ^ wordExp J ≤ max 1 t ^ (2 * m) :=
    (pow_le_pow_left₀ ht (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hT1 (wordExp_le_two_mul_length J))
  calc _ ≤ wordConst q J * t ^ wordExp J := hmom
    _ ≤ (decayConst q ^ m * nrm q (1 / (m.factorial : ℝ))) * max 1 t ^ (2 * m) :=
        mul_le_mul (wordConst_le hq J hJ) htT (pow_nonneg ht _)
          (mul_nonneg (pow_nonneg (by linarith [one_le_decayConst q]) _)
            (nrm_nonneg q (by positivity)))
    _ = _ := by ring

/-- **Factorial decay** of the level increment constants. -/
theorem wordIncr_le {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 0 ≤ T) :
    ∀ I : Word (d + 1), I ≠ [] →
    wordIncr q T I ≤ decayConst q ^ I.length * max 1 T ^ (2 * I.length) *
      nrm q (1 / ((I.length - 1).factorial : ℝ))
  | [], h => absurd rfl h
  | j :: I, _ => by
    have hC := one_le_decayConst q
    have hT1 : (1 : ℝ) ≤ max 1 T := le_max_left _ _
    have hTM : T ≤ max 1 T := le_max_right _ _
    by_cases hI : I = []
    · subst hI
      simp only [wordIncr, ↓reduceIte, List.length_cons, List.length_nil, zero_add, pow_one,
        Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one, nrm_one, mul_one]
      have hM2 : max 1 T ≤ max 1 T ^ (2 * 1) := by
        calc max 1 T = max 1 T ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hT1 (by norm_num)
      have hM1 : (1 : ℝ) ≤ max 1 T ^ 2 := one_le_pow₀ hT1
      split_ifs
      · calc T ≤ max 1 T ^ 2 := hTM.trans (by simpa using hM2)
          _ ≤ decayConst q * max 1 T ^ 2 := le_mul_of_one_le_left (by positivity) hC
      · have h1 : nrm q (gaussMoment q) ≤ decayConst q :=
          (le_max_right _ _).trans (le_max_right _ _)
        calc nrm q (gaussMoment q) ≤ decayConst q := h1
          _ ≤ decayConst q * max 1 T ^ 2 := le_mul_of_one_le_right (by linarith) hM1
    · set m := I.length with hm
      have hA := wordConst_nonneg hq I
      have hW := wordConst_le hq I hI
      have hN0 : 0 ≤ nrm q (1 / (m.factorial : ℝ)) := nrm_nonneg q (by positivity)
      have hTe : T ^ wordExp I ≤ max 1 T ^ (2 * m) :=
        (pow_le_pow_left₀ hT hTM _).trans (pow_le_pow_right₀ hT1 (wordExp_le_two_mul_length I))
      have hT2 : T ≤ max 1 T ^ 2 :=
        hTM.trans (by nlinarith)
      have hlen : (j :: I).length - 1 = m := by simp [m]
      rw [hlen]
      simp only [wordIncr, hI, ↓reduceIte, List.length_cons]
      have hD0 : 0 ≤ decayConst q := by linarith
      have key : wordConst q I * T ^ wordExp I ≤
          decayConst q ^ m * max 1 T ^ (2 * m) * nrm q (1 / (m.factorial : ℝ)) := by
        calc wordConst q I * T ^ wordExp I
            ≤ (decayConst q ^ m * nrm q (1 / (m.factorial : ℝ))) * max 1 T ^ (2 * m) :=
              mul_le_mul hW hTe (pow_nonneg hT _) (by positivity)
          _ = _ := by ring
      have hK0 : 0 ≤ decayConst q ^ m * max 1 T ^ (2 * m) * nrm q (1 / (m.factorial : ℝ)) := by
        positivity
      have hp : 0 ≤ wordConst q I * T ^ wordExp I := mul_nonneg hA (pow_nonneg hT _)
      split_ifs with hj
      · calc wordConst q I * T ^ wordExp I * T
            ≤ (decayConst q ^ m * max 1 T ^ (2 * m) * nrm q (1 / (m.factorial : ℝ))) *
                (decayConst q * max 1 T ^ 2) :=
              mul_le_mul key (hT2.trans (le_mul_of_one_le_left (by positivity) hC)) hT hK0
          _ = _ := by rw [pow_succ, mul_add, pow_add]; ring
      · have hE : itoEvenConst q ≤ decayConst q := (le_max_left _ _).trans (le_max_right _ _)
        calc itoEvenConst q * (wordConst q I * T ^ wordExp I)
            ≤ decayConst q * (decayConst q ^ m * max 1 T ^ (2 * m) *
                nrm q (1 / (m.factorial : ℝ))) * 1 := by
              rw [mul_one]; exact mul_le_mul hE key hp hD0
          _ ≤ decayConst q * (decayConst q ^ m * max 1 T ^ (2 * m) *
                nrm q (1 / (m.factorial : ℝ))) * max 1 T ^ 2 :=
              mul_le_mul_of_nonneg_left (one_le_pow₀ hT1) (by positivity)
          _ = _ := by rw [pow_succ, mul_add, pow_add]; ring

/-- `L^{2q}` increment bound for an Itô word coordinate on `[0, T]`. -/
theorem eLpNorm_itoWordIntegral_sub_le (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q) {T : ℝ}
    (hT : 0 ≤ T) (J : Word (d + 1)) (hJ : J ≠ []) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvT : v ≤ T) :
    eLpNorm (fun ω => itoWordIntegral B 0 v ω J - itoWordIntegral B 0 u ω J) (2 * q : ℕ) P ≤
      ENNReal.ofReal (Real.sqrt (wordIncr q T J * (v - u))) := by
  have hL := levelBound_itoWordIntegral (P := P) B hT J hJ
  have hm : MemLp (fun ω => itoWordIntegral B 0 v ω J - itoWordIntegral B 0 u ω J)
      (2 * q : ℕ) P :=
    (hL.memLp q hq v (hu.trans huv) hvT).sub (hL.memLp q hq u hu (huv.trans hvT))
  have hinc := hL.incr q hq u v hu huv hvT
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have h2q : ((2 * q : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * q ≠ 0 by omega)
  rw [hm.eLpNorm_eq_integral_rpow_norm h2q (ENNReal.natCast_ne_top _)]
  apply ENNReal.ofReal_le_ofReal
  set F : Ω → ℝ := fun ω => itoWordIntegral B 0 v ω J - itoWordIntegral B 0 u ω J
  have hI : ∫ ω, ‖F ω‖ ^ (((2 * q : ℕ) : ℝ≥0∞).toReal) ∂P = ∫ ω, F ω ^ (2 * q) ∂P := by
    congr 1; funext ω
    rw [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, hev.pow_abs]
  have h0 : 0 ≤ ∫ ω, F ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
  rw [hI, ENNReal.toReal_natCast]
  have hsq : (∫ ω, F ω ^ (2 * q) ∂P) ^ (((2 * q : ℕ) : ℝ))⁻¹ =
      Real.sqrt (nrm q (∫ ω, F ω ^ (2 * q) ∂P)) := by
    rw [Real.sqrt_eq_rpow, nrm, ← Real.rpow_mul h0]
    congr 1; push_cast; field_simp
  rw [hsq]
  exact Real.sqrt_le_sqrt hinc

/-- Superexponential decay: `Σ Kⁿ (1/⌊n/2⌋!)^{1/s} < ∞`. -/
theorem summable_pow_mul_inv_factorial_half {K : ℝ} (hK : 0 ≤ K) {s : ℕ} (hs : s ≠ 0) :
    Summable (fun n : ℕ => K ^ n * ((1 : ℝ) / ((n / 2).factorial : ℝ)) ^ ((s : ℝ)⁻¹)) := by
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hK'0 : 0 ≤ K' := by linarith
  set x : ℝ := (4 * K' ^ 2) ^ s with hx
  have hx0 : 0 ≤ x := by positivity
  set M := Real.exp x
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_two).mul_left (K' * M ^ ((s : ℝ)⁻¹) * 2))
  set m := n / 2
  have hn : n ≤ 2 * m + 1 := by omega
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  -- `K'^{2m} (1/m!)^{1/s} ≤ M^{1/s} / 4^m`
  have hcore : K' ^ (2 * m) * ((1 : ℝ) / (m.factorial : ℝ)) ^ ((s : ℝ)⁻¹) ≤
      M ^ ((s : ℝ)⁻¹) * (1 / 4 ^ m) := by
    have hA : K' ^ (2 * m) = ((K' ^ (2 * m)) ^ s) ^ ((s : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) hs).symm
    have hB : (1 / 4 ^ m : ℝ) = ((1 / 4 ^ m) ^ s) ^ ((s : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) hs).symm
    rw [hA, hB, ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have hle : x ^ m / (m.factorial : ℝ) ≤ M := Real.pow_div_factorial_le_exp _ hx0 m
    have e1 : (K' ^ (2 * m)) ^ s * (1 / (m.factorial : ℝ)) =
        x ^ m / (m.factorial : ℝ) * (1 / 4 ^ m) ^ s := by
      have h4 : (4 : ℝ) ^ (m * s) ≠ 0 := by positivity
      have k1 : x ^ m * (1 / 4 ^ m) ^ s =
          4 ^ (m * s) * K' ^ (2 * m * s) * (1 / 4 ^ (m * s)) := by
        rw [hx]; ring
      have k2 : x ^ m * (1 / 4 ^ m) ^ s = (K' ^ (2 * m)) ^ s := by
        rw [k1, ← pow_mul]; field_simp
      rw [div_mul_eq_mul_div, k2]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hKn : K ^ n ≤ K' * K' ^ (2 * m) :=
    (pow_le_pow_left₀ hK (le_max_left _ _) n).trans
      ((pow_le_pow_right₀ hK'1 hn).trans_eq (by rw [pow_succ]; ring))
  have h4 : (1 / 4 ^ m : ℝ) ≤ 2 * (1 / 2) ^ n := by
    have h2 : (2 : ℝ) ^ n ≤ 2 * 4 ^ m := by
      calc (2 : ℝ) ^ n ≤ 2 ^ (2 * m + 1) := pow_le_pow_right₀ (by norm_num) hn
        _ = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
    have h3 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ n) h2
    calc (1 / 4 ^ m : ℝ) = 2 * (1 / (2 * 4 ^ m)) := by field_simp
      _ ≤ 2 * (1 / 2 ^ n) := by linarith
      _ = _ := by rw [one_div_pow]
  have hF0 : 0 ≤ ((1 : ℝ) / (m.factorial : ℝ)) ^ ((s : ℝ)⁻¹) := by positivity
  calc K ^ n * ((1 : ℝ) / (m.factorial : ℝ)) ^ ((s : ℝ)⁻¹)
      ≤ K' * (K' ^ (2 * m) * ((1 : ℝ) / (m.factorial : ℝ)) ^ ((s : ℝ)⁻¹)) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKn hF0
    _ ≤ K' * (M ^ ((s : ℝ)⁻¹) * (2 * (1 / 2) ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ hK'0
        exact hcore.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    _ = _ := by ring

omit [IsProbabilityMeasure P] in
/-- `L^N` bound for a sum of non-negative terms: `∫⁻ (Σ Yₙ)^N ≤ (Σ bₙ)^N`. -/
theorem lintegral_tsum_rpow_le {Y : ℕ → Ω → ℝ} (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (hYm : ∀ n, Measurable (Y n)) {N : ℕ} (hN : 1 ≤ N) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, eLpNorm (Y n) N P ≤ ENNReal.ofReal (b n)) (hbs : Summable b) :
    ∫⁻ ω, (∑' n, ENNReal.ofReal (Y n ω)) ^ (N : ℝ) ∂P ≤ ENNReal.ofReal (∑' n, b n) ^ (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set G : Ω → ℝ≥0∞ := fun ω => ∑' n, ENNReal.ofReal (Y n ω) with hG
  have hGm : Measurable G := Measurable.tsum fun n => (hYm n).ennreal_ofReal
  set F : ℕ → Ω → ℝ≥0∞ := fun k ω => ∑ n ∈ Finset.range k, ENNReal.ofReal (Y n ω) with hF
  set Mb : ℝ≥0∞ := ENNReal.ofReal (∑' n, b n)
  -- partial sums are bounded in `L^N`
  have hpart : ∀ k, ∫⁻ ω, F k ω ^ (N : ℝ) ∂P ≤ Mb ^ (N : ℝ) := by
    intro k
    set S : Ω → ℝ := fun ω => ∑ n ∈ Finset.range k, Y n ω
    have hSm : Measurable S := Finset.measurable_sum _ fun n _ => hYm n
    have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun n _ => hY0 n ω
    have hFS : ∀ ω, F k ω = ‖S ω‖ₑ := by
      intro ω
      rw [Real.enorm_eq_ofReal (hS0 ω), ENNReal.ofReal_sum_of_nonneg fun n _ => hY0 n ω]
    have hle : eLpNorm S N P ≤ Mb := by
      have hS : S = ∑ n ∈ Finset.range k, Y n := by funext ω; simp [S]
      calc eLpNorm S N P ≤ ∑ n ∈ Finset.range k, eLpNorm (Y n) N P := by
            rw [hS]; exact eLpNorm_sum_le (by exact_mod_cast hN)
        _ ≤ ∑ n ∈ Finset.range k, ENNReal.ofReal (b n) := Finset.sum_le_sum fun n _ => hb n
        _ = ENNReal.ofReal (∑ n ∈ Finset.range k, b n) :=
            (ENNReal.ofReal_sum_of_nonneg fun n _ => hb0 n).symm
        _ ≤ Mb := ENNReal.ofReal_le_ofReal (hbs.sum_le_tsum _ fun n _ => hb0 n)
    have hNe : ((N : ℝ≥0∞)) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hE := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := P) hNe (ENNReal.natCast_ne_top N)
      hSm.aestronglyMeasurable
    rw [ENNReal.toReal_natCast] at hE
    have hI : ∫⁻ ω, F k ω ^ (N : ℝ) ∂P = eLpNorm S N P ^ (N : ℝ) := by
      rw [hE, ← ENNReal.rpow_mul, one_div_mul_cancel hN0.ne', ENNReal.rpow_one]
      simp_rw [hFS]
    rw [hI]
    exact ENNReal.rpow_le_rpow hle hN0.le
  -- monotone convergence
  have hlim : ∫⁻ ω, G ω ^ (N : ℝ) ∂P ≤ Mb ^ (N : ℝ) := by
    have ht := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
      (f := fun k ω => F k ω ^ (N : ℝ)) (F := fun ω => G ω ^ (N : ℝ))
      (fun k => ((Finset.measurable_sum _ fun n _ => (hYm n).ennreal_ofReal).pow_const _
        ).aemeasurable)
      (Eventually.of_forall fun ω => fun k l hkl => ENNReal.rpow_le_rpow
        (Finset.sum_le_sum_of_subset (Finset.range_mono hkl)) hN0.le)
      (Eventually.of_forall fun ω =>
        ((ENNReal.continuous_rpow_const).tendsto _).comp (ENNReal.tendsto_nat_tsum _))
    exact le_of_tendsto' ht hpart
  exact hlim

/-- **Summation in `L^N`.** Non-negative measurable `Yₙ` with `Σ ‖Yₙ‖_N < ∞` are a.s. summable,
and the `p`-th power of the sum is integrable for `1 ≤ p ≤ N`. -/
theorem summable_integrable_of_eLpNorm_le {Y : ℕ → Ω → ℝ} (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (hYm : ∀ n, Measurable (Y n)) {N : ℕ} (hN : 1 ≤ N) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, eLpNorm (Y n) N P ≤ ENNReal.ofReal (b n)) (hbs : Summable b) {p : ℝ}
    (hp : 1 ≤ p) (hpN : p ≤ N) :
    (∀ᵐ ω ∂P, Summable (fun n => Y n ω)) ∧
      Integrable (fun ω => (∑' n, Y n ω) ^ p) P := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set G : Ω → ℝ≥0∞ := fun ω => ∑' n, ENNReal.ofReal (Y n ω) with hG
  have hGm : Measurable G := Measurable.tsum fun n => (hYm n).ennreal_ofReal
  set Mb : ℝ≥0∞ := ENNReal.ofReal (∑' n, b n)
  have hlim : ∫⁻ ω, G ω ^ (N : ℝ) ∂P ≤ Mb ^ (N : ℝ) :=
    lintegral_tsum_rpow_le hY0 hYm hN hb0 hb hbs
  have hMb : Mb ^ (N : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hN0.le ENNReal.ofReal_ne_top
  have hGfin : ∀ᵐ ω ∂P, G ω ≠ ⊤ := by
    have := ae_lt_top (hGm.pow_const (N : ℝ)) (ne_top_of_le_ne_top hMb hlim)
    filter_upwards [this] with ω hω h
    rw [h, ENNReal.top_rpow_of_pos hN0] at hω
    exact lt_irrefl _ hω
  have hsum : ∀ᵐ ω ∂P, Summable (fun n => Y n ω) := by
    filter_upwards [hGfin] with ω hω
    have := ENNReal.summable_toReal hω
    simpa [ENNReal.toReal_ofReal (hY0 _ ω)] using this
  have htsum : ∀ᵐ ω ∂P, ∑' n, Y n ω = (G ω).toReal := by
    filter_upwards [hGfin] with ω hω
    rw [hG, ENNReal.tsum_toReal_eq fun n => ENNReal.ofReal_ne_top]
    simp [ENNReal.toReal_ofReal (hY0 _ ω)]
  refine ⟨hsum, ?_⟩
  have hae : (fun ω => (∑' n, Y n ω) ^ p) =ᵐ[P] fun ω => (G ω).toReal ^ p := by
    filter_upwards [htsum] with ω h; rw [h]
  refine Integrable.congr ?_ hae.symm
  refine ⟨(hGm.ennreal_toReal.pow_const p).aestronglyMeasurable, ?_⟩
  have hbd : ∀ᵐ ω ∂P, ‖(G ω).toReal ^ p‖ₑ ≤ 1 + G ω ^ (N : ℝ) := by
    filter_upwards [hGfin] with ω hω
    set x := (G ω).toReal
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hx0 p)]
    have hGx : G ω = ENNReal.ofReal x := (ENNReal.ofReal_toReal hω).symm
    rw [hGx, ENNReal.ofReal_rpow_of_nonneg hx0 hN0.le, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg hx0 _)]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total x 1 with hx1 | hx1
    · have := Real.rpow_le_one hx0 hx1 (by linarith : (0 : ℝ) ≤ p)
      linarith [Real.rpow_nonneg hx0 (N : ℝ)]
    · have := Real.rpow_le_rpow_of_exponent_le hx1 hpN
      linarith
  calc ∫⁻ ω, ‖(G ω).toReal ^ p‖ₑ ∂P ≤ ∫⁻ ω, (1 + G ω ^ (N : ℝ)) ∂P := lintegral_mono_ae hbd
    _ = 1 + ∫⁻ ω, G ω ^ (N : ℝ) ∂P := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_lt hlim hMb.lt_top⟩

/-- Real-valued form: `∫ (Σ Yₙ)^N ≤ (Σ bₙ)^N`, given the sum is a.s. summable. -/
theorem integral_tsum_pow_le {Y : ℕ → Ω → ℝ} (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (hYm : ∀ n, Measurable (Y n)) {N : ℕ} (hN : 1 ≤ N) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, eLpNorm (Y n) N P ≤ ENNReal.ofReal (b n)) (hbs : Summable b) :
    ∫ ω, (∑' n, Y n ω) ^ N ∂P ≤ (∑' n, b n) ^ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := (summable_integrable_of_eLpNorm_le hY0 hYm hN hb0 hb hbs le_rfl
    (by exact_mod_cast hN)).1
  have hlim := lintegral_tsum_rpow_le hY0 hYm hN hb0 hb hbs
  have hS0 : ∀ ω, 0 ≤ ∑' n, Y n ω := fun ω => tsum_nonneg fun n => hY0 n ω
  have hSm : Measurable fun ω => ∑' n, Y n ω := Measurable.tsum hYm
  have hB0 : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => pow_nonneg (hS0 ω) N)
    (hSm.pow_const N).aestronglyMeasurable]
  rw [← ENNReal.toReal_ofReal (pow_nonneg hB0 N)]
  apply ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal ((∑' n, Y n ω) ^ N) =
      (∑' n, ENNReal.ofReal (Y n ω)) ^ (N : ℝ) := by
    filter_upwards [hsum] with ω hω
    rw [ENNReal.ofReal_pow (hS0 ω), ENNReal.ofReal_tsum_of_nonneg (fun n => hY0 n ω) hω,
      ENNReal.rpow_natCast]
  rw [lintegral_congr_ae hae, ENNReal.ofReal_pow hB0, ← ENNReal.rpow_natCast]
  exact hlim

end SignatureVolatility
