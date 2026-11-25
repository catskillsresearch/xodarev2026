module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ItoCalculusKit.LevelDecay
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace SignatureVolatility

/-!
# The paper's Stratonovich signature `Ŵ_{s,t}` of `X = (t, W_t)`

`itoWordIntegral (j :: I)` integrates the *first* letter outermost (latest in time), whereas
the tensor-algebra conventions used by the paper (`concat`, `rightShift`, `riccatiOp`,
`dŴ = Ŵ ⊗ ∘dX`) make the *last* letter the latest.  `paperSig2` therefore reads the
Stratonovich word integral of the reversed word:
`⟨e_{i₁⋯iₙ}, Ŵ_{s,t}⟩ = ∫_{s<u₁<⋯<uₙ<t} ∘dX^{i₁}_{u₁} ⋯ ∘dX^{iₙ}_{uₙ}`.
Each Itô level `≥ 2` is its adapted continuous version (`contVersion`), so `Ŵ` is the
continuous signature process of the paper (up to the almost-sure continuity proved later).

Chen and shuffle (`paperSig2_chen`, `paperSig2_shuffle`) are proved in `PaperSigChen`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Paper Stratonovich signature of the time-extended Brownian path (iterated integrals). -/
def paperSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I.reverse⟩

lemma paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (I : Word (d + 1)) :
    (paperSig2 B s t ω).coeff I = stratWordIntegral B s t ω I.reverse := rfl

lemma paperSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [] = 1 := by
  simp [paperSig2, stratWordIntegral, itoWordIntegral, stratItoCorrection]

lemma paperSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [0] = t - s :=
  stratWordIntegral_time B s t ω

lemma paperSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (paperSig2 B s t ω).coeff [i.succ] = MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  stratWordIntegral_space B s t ω i

lemma measurable_paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (paperSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral B s t I.reverse

lemma measurable_paperSig2_coeff_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => (paperSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral_pathFiltration B hs hst htT I.reverse

/-- Level 2, two different letters: the paper order puts the first letter earliest. -/
lemma paperSig2_pair (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i j : Fin (d + 1)) :
    (paperSig2 B s t ω).coeff [i, j] = stratWordIntegral B s t ω [j, i] := rfl

/-! ## Regularity of the coordinates from the level-wise Itô bounds -/

/-- Almost surely, every Itô word coordinate is continuous on `[0, T]`. -/
lemma ae_continuousOn_itoWordIntegral (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ J : Word (d + 1),
      ContinuousOn (fun t => itoWordIntegral B 0 t ω J) (Set.Icc 0 T) := by
  rw [ae_all_iff]
  intro J
  by_cases hJ : J = []
  · subst hJ
    exact Filter.Eventually.of_forall fun ω => by
      simpa [itoWordIntegral_empty] using continuousOn_const
  · exact (levelBound_itoWordIntegral B hT J hJ).cont

/-- Every Itô word coordinate is in every even `L^{2q}`, `q ≥ 2`. -/
lemma memLp_itoWordIntegral (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (J : Word (d + 1))
    {q : ℕ} (hq : 2 ≤ q) : MemLp (fun ω => itoWordIntegral B 0 t ω J) (2 * q : ℕ) P := by
  by_cases hJ : J = []
  · subst hJ; simpa [itoWordIntegral_empty] using memLp_const (1 : ℝ)
  · exact (levelBound_itoWordIntegral B ht J hJ).memLp q hq t ht le_rfl

lemma continuousOn_stratItoCorrection (B : MultiBrownian Ω P d) {T : ℝ} {ω : Ω}
    (hω : ∀ J : Word (d + 1), ContinuousOn (fun t => itoWordIntegral B 0 t ω J) (Set.Icc 0 T))
    (K : Word (d + 1)) :
    ContinuousOn (fun t => stratItoCorrection B 0 t ω K) (Set.Icc 0 T) := by
  match K with
  | [] => exact continuousOn_const
  | [_] => exact continuousOn_const
  | _ :: _ :: _ =>
    exact continuousOn_finsetSum _ fun n _ => continuousOn_finsetSum _ fun J _ =>
      continuousOn_const.mul (hω J)

lemma memLp_stratItoCorrection (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (K : Word (d + 1)) {q : ℕ} (hq : 2 ≤ q) :
    MemLp (fun ω => stratItoCorrection B 0 t ω K) (2 * q : ℕ) P := by
  match K with
  | [] => exact memLp_const 0
  | [_] => exact memLp_const 0
  | _ :: _ :: _ =>
    simp only [stratItoCorrection]
    exact memLp_finsetSum _ fun n _ => memLp_finsetSum _ fun J _ =>
      (memLp_itoWordIntegral B ht J hq).const_mul _

/-- Almost surely, every coordinate of `Ŵ_{0,·}` is continuous on `[0, T]`. -/
theorem ae_continuousOn_paperSig2_coeff (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ I : Word (d + 1),
      ContinuousOn (fun t => (paperSig2 B 0 t ω).coeff I) (Set.Icc 0 T) := by
  filter_upwards [ae_continuousOn_itoWordIntegral B hT] with ω hω I
  simp only [paperSig2_coeff, stratWordIntegral]
  exact (hω _).add (continuousOn_stratItoCorrection B hω _)

/-- Every coordinate of `Ŵ_{0,t}` has finite moments of every even order `2q ≥ 4`. -/
theorem memLp_paperSig2_coeff (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (I : Word (d + 1)) {q : ℕ} (hq : 2 ≤ q) :
    MemLp (fun ω => (paperSig2 B 0 t ω).coeff I) (2 * q : ℕ) P := by
  simp only [paperSig2_coeff, stratWordIntegral]
  exact (memLp_itoWordIntegral B ht _ hq).add (memLp_stratItoCorrection B ht _ hq)

/-! ## Level-wise `L^{2q}` bounds for `Ŵ` (towards Prop. 12) -/

lemma card_wordsOfLength (d n : ℕ) : ((wordsOfLength d n).card : ℝ) = (d : ℝ) ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    have h := wordsOfLength.succ (d := d) n (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fin] at h
    rw [h, ih, pow_succ]; ring

/-- The level-`n` profile `(C_q max(1,t)²)ⁿ (1/⌊n/2⌋!)^{1/(2q)}`. -/
def momBound (q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  (decayConst q * max 1 t ^ 2) ^ n * ((1 : ℝ) / ((n / 2).factorial : ℝ)) ^ (((2 * q : ℕ) : ℝ)⁻¹)

lemma one_le_decayConst_mul (q : ℕ) (t : ℝ) : 1 ≤ decayConst q * max 1 t ^ 2 :=
  one_le_mul_of_one_le_of_one_le (one_le_decayConst q) (one_le_pow₀ (le_max_left _ _))

lemma momBound_nonneg (q : ℕ) (t : ℝ) (n : ℕ) : 0 ≤ momBound q t n :=
  mul_nonneg (pow_nonneg (by linarith [one_le_decayConst_mul q t]) _) (by positivity)

lemma summable_mul_momBound (q : ℕ) (hq : 2 ≤ q) (t : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    Summable (fun n => K ^ n * momBound q t n) := by
  have hD := one_le_decayConst_mul q t
  have := summable_pow_mul_inv_factorial_half (K := K * (decayConst q * max 1 t ^ 2))
    (mul_nonneg hK (by linarith)) (s := 2 * q) (by omega)
  refine this.congr fun n => ?_
  simp only [momBound, mul_pow]; ring

lemma eLpNorm_itoWordIntegral_le_momBound (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q)
    {t : ℝ} (ht : 0 ≤ t) {J : Word (d + 1)} (hJ : J ≠ []) {n : ℕ} (h1 : n ≤ 2 * J.length)
    (h2 : J.length ≤ n) :
    eLpNorm (fun ω => itoWordIntegral B 0 t ω J) (2 * q : ℕ) P ≤
      ENNReal.ofReal (momBound q t n) := by
  refine (eLpNorm_itoWordIntegral_le B hq ht J hJ).trans (ENNReal.ofReal_le_ofReal ?_)
  set m := J.length
  set D := decayConst q * max 1 t ^ 2
  have hD : 1 ≤ D := one_le_decayConst_mul q t
  set z : ℝ := (1 : ℝ) / ((n / 2).factorial : ℝ)
  have hz : 0 ≤ z := by positivity
  rw [← Real.sqrt_sq (momBound_nonneg q t n)]
  apply Real.sqrt_le_sqrt
  have hsq : momBound q t n ^ 2 = D ^ (2 * n) * nrm q z := by
    simp only [momBound]
    rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (z ^ _), ← Real.rpow_mul hz, nrm]
    congr 2
    · ring
    · push_cast; field_simp
  rw [hsq]
  have hfac : (1 : ℝ) / (m.factorial : ℝ) ≤ z := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.factorial_le (by omega)
  calc decayConst q ^ m * max 1 t ^ (2 * m) * nrm q (1 / (m.factorial : ℝ))
      = D ^ m * nrm q (1 / (m.factorial : ℝ)) := by simp only [D]; rw [mul_pow, ← pow_mul]
    _ ≤ D ^ (2 * n) * nrm q z :=
        mul_le_mul (pow_le_pow_right₀ hD (by omega)) (nrm_mono (by positivity) hfac)
          (nrm_nonneg q (by positivity)) (by positivity)

lemma stratItoCorrection_eq_sum (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω)
    {K : Word (d + 1)} (hK : 2 ≤ K.length) :
    stratItoCorrection B 0 t ω K = ∑ m ∈ Finset.range K.length,
      ∑ J ∈ wordsOfLength (d + 1) m, stratItoCoeff K J * itoWordIntegral B 0 t ω J := by
  match K, hK with
  | _ :: _ :: _, _ => rfl

/-- `L^{2q}` bound for one coordinate of `Ŵ_{0,t}`. -/
theorem eLpNorm_paperSig2_coeff_le (B : MultiBrownian Ω P d) {q : ℕ} (hq : 2 ≤ q) {t : ℝ}
    (ht : 0 ≤ t) (I : Word (d + 1)) :
    eLpNorm (fun ω => (paperSig2 B 0 t ω).coeff I) (2 * q : ℕ) P ≤
      ENNReal.ofReal ((1 + I.length * ((d : ℝ) + 1) ^ I.length * 2 ^ I.length) *
        momBound q t I.length) := by
  have h1q : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  by_cases hI : I = []
  · subst hI
    simp only [paperSig2_empty, List.length_nil, CharP.cast_eq_zero, pow_zero, zero_mul,
      add_zero, one_mul, momBound, Nat.zero_div, Nat.factorial_zero, Nat.cast_one, div_one,
      Real.one_rpow]
    refine (eLpNorm_le_of_ae_bound (C := 1) aestronglyMeasurable_const
      (Eventually.of_forall fun _ => by simp)).trans ?_
    simp
  set n := I.length with hn
  set K := I.reverse with hKdef
  have hKn : K.length = n := by simp [K, n]
  have hK : K ≠ [] := by simpa [K] using hI
  have hn1 : 1 ≤ n := List.length_pos_iff.2 hI
  have hito : eLpNorm (fun ω => itoWordIntegral B 0 t ω K) (2 * q : ℕ) P ≤
      ENNReal.ofReal (momBound q t n) :=
    eLpNorm_itoWordIntegral_le_momBound B hq ht hK (by omega) hKn.le
  have hcorr : eLpNorm (fun ω => stratItoCorrection B 0 t ω K) (2 * q : ℕ) P ≤
      ENNReal.ofReal (n * ((d : ℝ) + 1) ^ n * 2 ^ n * momBound q t n) := by
    by_cases hK2 : K.length ≤ 1
    · have : (fun ω => stratItoCorrection B 0 t ω K) = fun _ => (0 : ℝ) := by
        funext ω; exact stratItoCorrection_of_length_le_one B 0 t ω K hK2
      rw [this]; simp
    have hK2' : 2 ≤ K.length := by omega
    set c : ℝ := 2 ^ n * momBound q t n
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) (momBound_nonneg q t n)
    have hfun : (fun ω => stratItoCorrection B 0 t ω K) = ∑ m ∈ Finset.range n,
        ∑ J ∈ wordsOfLength (d + 1) m,
          fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J := by
      funext ω
      rw [stratItoCorrection_eq_sum B t ω hK2', hKn]
      simp [Finset.sum_apply]
    have hterm : ∀ m ∈ Finset.range n, ∀ J ∈ wordsOfLength (d + 1) m,
        eLpNorm (fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J) (2 * q : ℕ) P ≤
          ENNReal.ofReal c := by
      intro m hm J hJ
      have hJm : J.length = m := wordsOfLength.mem.1 hJ
      have hm' : m < n := Finset.mem_range.1 hm
      by_cases ha : stratItoCoeff K J = 0
      · simp [ha]
      have h2 := length_le_two_mul_of_stratItoCoeff_ne_zero ha
      have hJne : J ≠ [] := by
        rintro rfl; rw [List.length_nil] at h2; omega
      have e : (fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J) =
          stratItoCoeff K J • fun ω => itoWordIntegral B 0 t ω J := by
        funext ω; simp
      rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (stratItoCoeff_nonneg K J)]
      have hA : ENNReal.ofReal (stratItoCoeff K J) ≤ ENNReal.ofReal (2 ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [hKn] using stratItoCoeff_le K J
      calc ENNReal.ofReal (stratItoCoeff K J) * eLpNorm (fun ω => itoWordIntegral B 0 t ω J)
            (2 * q : ℕ) P ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (momBound q t n) :=
            mul_le_mul' hA (eLpNorm_itoWordIntegral_le_momBound B hq ht hJne
              (by rw [← hKn]; exact h2) (by omega))
        _ = ENNReal.ofReal c := (ENNReal.ofReal_mul (by positivity)).symm
    rw [hfun]
    calc eLpNorm (∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
          fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J) (2 * q : ℕ) P
        ≤ ∑ m ∈ Finset.range n, eLpNorm (∑ J ∈ wordsOfLength (d + 1) m,
          fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J) (2 * q : ℕ) P :=
          eLpNorm_sum_le h1q
      _ ≤ ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
          eLpNorm (fun ω => stratItoCoeff K J * itoWordIntegral B 0 t ω J) (2 * q : ℕ) P :=
          Finset.sum_le_sum fun m _ => eLpNorm_sum_le h1q
      _ ≤ ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m, ENNReal.ofReal c :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun J hJ => hterm m hm J hJ
      _ = ENNReal.ofReal (∑ m ∈ Finset.range n, ((wordsOfLength (d + 1) m).card : ℝ) * c) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg (wordsOfLength (d + 1) m).card),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (n * ((d : ℝ) + 1) ^ n * 2 ^ n * momBound q t n) := by
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
  have hsplit : (fun ω => (paperSig2 B 0 t ω).coeff I) =
      (fun ω => itoWordIntegral B 0 t ω K) + fun ω => stratItoCorrection B 0 t ω K := by
    funext ω; simp [paperSig2_coeff, stratWordIntegral, K]
  rw [hsplit]
  refine (eLpNorm_add_le h1q).trans ?_
  calc _ ≤ ENNReal.ofReal (momBound q t n) +
        ENNReal.ofReal (n * ((d : ℝ) + 1) ^ n * 2 ^ n * momBound q t n) := add_le_add hito hcorr
    _ = _ := by
        rw [← ENNReal.ofReal_add (momBound_nonneg q t n)
          (by have := momBound_nonneg q t n; positivity)]
        congr 1; ring

/-! ## Paper properties of `paperSig2` (holes, step 3 of the true-signature refactor) -/

/-- **Paper Proposition 12 / Appendix A**: factorial level control of the Brownian signature
against weights of at most geometric growth. -/
theorem paperSig2_factorial_moment_control (B : MultiBrownian Ω P d) (p : ℝ) (hp : 1 ≤ p)
    (w_fn : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w_fn n) (hgeom : ∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, Summable (fun n : ℕ => w_fn n * (paperSig2 B 0 t ω).levelNorm n)) ∧
      Integrable (fun ω => (∑' n : ℕ, w_fn n * (paperSig2 B 0 t ω).levelNorm n) ^ p) P := by
  obtain ⟨r, hr⟩ := hgeom
  set q : ℕ := max 2 ⌈p⌉₊ with hqdef
  have hq : 2 ≤ q := le_max_left _ _
  have hpN : p ≤ ((2 * q : ℕ) : ℝ) := by
    have h1 : p ≤ (⌈p⌉₊ : ℝ) := Nat.le_ceil p
    have h2 : (⌈p⌉₊ : ℝ) ≤ q := by exact_mod_cast le_max_right _ _
    push_cast; linarith
  set R := |r|
  have hR : 0 ≤ R := abs_nonneg r
  have hwR : ∀ n, w_fn n ≤ R ^ n := fun n =>
    (hr n).trans ((le_abs_self _).trans (abs_pow r n).le)
  set Y : ℕ → Ω → ℝ := fun n ω => w_fn n * (paperSig2 B 0 t ω).levelNorm n with hY
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω =>
    mul_nonneg (hw0 n) (ExtTensorAlgebra.levelNorm.nonneg _ _)
  have hLm : ∀ n, Measurable (fun ω => (paperSig2 B 0 t ω).levelNorm n) := by
    intro n
    simp only [ExtTensorAlgebra.levelNorm, ExtTensorAlgebra.levelNormSq]
    exact (Finset.measurable_sum _ fun I _ =>
      (measurable_paperSig2_coeff B 0 t I).pow_const 2).sqrt
  have hYm : ∀ n, Measurable (Y n) := fun n => measurable_const.mul (hLm n)
  set b : ℕ → ℝ := fun n => R ^ n * (((d : ℝ) + 1) ^ n *
    ((1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * momBound q t n)) with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n => by
    have := momBound_nonneg q t n; positivity
  have h1q : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hbY : ∀ n, eLpNorm (Y n) (2 * q : ℕ) P ≤ ENNReal.ofReal (b n) := by
    intro n
    set c : ℝ := (1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n) * momBound q t n
    have hc0 : 0 ≤ c := by have := momBound_nonneg q t n; positivity
    have hpt : ∀ ω, ‖Y n ω‖ ≤ w_fn n * ∑ I ∈ wordsOfLength (d + 1) n,
        ‖(paperSig2 B 0 t ω).coeff I‖ := by
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hY0 n ω)]
      apply mul_le_mul_of_nonneg_left _ (hw0 n)
      simp only [ExtTensorAlgebra.levelNorm, ExtTensorAlgebra.levelNormSq]
      rw [← Real.sqrt_sq (Finset.sum_nonneg fun I _ => norm_nonneg _)]
      apply Real.sqrt_le_sqrt
      calc ∑ I ∈ wordsOfLength (d + 1) n, (paperSig2 B 0 t ω).coeff I ^ 2
          = ∑ I ∈ wordsOfLength (d + 1) n, ‖(paperSig2 B 0 t ω).coeff I‖ ^ 2 := by
            simp [Real.norm_eq_abs, sq_abs]
        _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun I _ => norm_nonneg _
    refine (eLpNorm_mono_real (hYm n).aestronglyMeasurable hpt).trans ?_
    have e : (fun ω => w_fn n * ∑ I ∈ wordsOfLength (d + 1) n,
        ‖(paperSig2 B 0 t ω).coeff I‖) = w_fn n • ∑ I ∈ wordsOfLength (d + 1) n,
          fun ω => ‖(paperSig2 B 0 t ω).coeff I‖ := by
      funext ω; simp [Finset.sum_apply]
    rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw0 n)]
    have hsum : eLpNorm (∑ I ∈ wordsOfLength (d + 1) n,
        fun ω => ‖(paperSig2 B 0 t ω).coeff I‖) (2 * q : ℕ) P ≤
          ENNReal.ofReal (((d : ℝ) + 1) ^ n * c) := by
      refine (eLpNorm_sum_le h1q).trans ?_
      calc ∑ I ∈ wordsOfLength (d + 1) n, eLpNorm (fun ω => ‖(paperSig2 B 0 t ω).coeff I‖)
            (2 * q : ℕ) P
          ≤ ∑ _I ∈ wordsOfLength (d + 1) n, ENNReal.ofReal c := by
            apply Finset.sum_le_sum
            intro I hI
            have hIn : I.length = n := wordsOfLength.mem.1 hI
            rw [eLpNorm_norm _ (measurable_paperSig2_coeff B 0 t I).aestronglyMeasurable]
            have := eLpNorm_paperSig2_coeff_le B hq ht I
            rw [hIn] at this
            exact this
        _ = ENNReal.ofReal (((d : ℝ) + 1) ^ n * c) := by
            have hcard : ((wordsOfLength (d + 1) n).card : ℝ) = ((d : ℝ) + 1) ^ n := by
              rw [card_wordsOfLength]; push_cast; rfl
            rw [Finset.sum_const, nsmul_eq_mul, ← hcard,
              ENNReal.ofReal_mul (Nat.cast_nonneg (wordsOfLength (d + 1) n).card),
              ENNReal.ofReal_natCast]
    calc ENNReal.ofReal (w_fn n) * eLpNorm (∑ I ∈ wordsOfLength (d + 1) n,
          fun ω => ‖(paperSig2 B 0 t ω).coeff I‖) (2 * q : ℕ) P
        ≤ ENNReal.ofReal (R ^ n) * ENNReal.ofReal (((d : ℝ) + 1) ^ n * c) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (hwR n)) hsum
      _ = ENNReal.ofReal (b n) := (ENNReal.ofReal_mul (by positivity)).symm
  have hbs : Summable b := by
    have h1 := summable_mul_momBound q hq t (K := R * ((d : ℝ) + 1)) (by positivity)
    have h2 := summable_mul_momBound q hq t (K := 2 * (R * ((d : ℝ) + 1) ^ 2 * 2))
      (by positivity)
    refine Summable.of_nonneg_of_le hb0 (fun n => ?_) (h1.add h2)
    have hM := momBound_nonneg q t n
    have hn2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have hK0 : 0 ≤ (R * ((d : ℝ) + 1) ^ 2 * 2) ^ n := by positivity
    calc b n = (R * ((d : ℝ) + 1)) ^ n * momBound q t n +
          (n : ℝ) * ((R * ((d : ℝ) + 1) ^ 2 * 2) ^ n * momBound q t n) := by
          simp only [b]; rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ (R * ((d : ℝ) + 1)) ^ n * momBound q t n +
          (2 * (R * ((d : ℝ) + 1) ^ 2 * 2)) ^ n * momBound q t n := by
          have h3 : (n : ℝ) * ((R * ((d : ℝ) + 1) ^ 2 * 2) ^ n * momBound q t n) ≤
              (2 * (R * ((d : ℝ) + 1) ^ 2 * 2)) ^ n * momBound q t n := by
            have h4 := mul_le_mul_of_nonneg_right hn2 (mul_nonneg hK0 hM)
            rw [mul_pow (2 : ℝ)]
            linarith
          linarith
  exact summable_integrable_of_eLpNorm_le hY0 hYm (by omega) hb0 hbY hbs hp hpN

end SignatureVolatility
