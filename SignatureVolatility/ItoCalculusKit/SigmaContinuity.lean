module

public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.ItoCalculusKit.SigmaBounds
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.ProlongedBrownianSetup.WHat


@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SignatureVolatility

/-!
# Continuity of the signature volatility

`continuousOn_dualPairing_of_levelNorm_le` is the Weierstrass M-test for `s ↦ ⟨ℓ, X_s⟩` under H1
given levelwise continuity and a summable level bound. For the paper's Brownian Stratonovich
signature, `σ_s(ω) = ⟨ℓ, Ŵ_s(ω)⟩` is continuous on `[0, T]` almost surely
(`ae_continuousOn_sigma_of_brownian`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Pathwise continuity of the signature volatility -/

/-- The time-augmented increment `(s, W_s) - (0, W_0)` is continuous in `s` along every path. -/
lemma continuous_wAug_sub (B : MultiBrownian Ω P d) (ω : Ω) (j : Fin (d + 1)) :
    Continuous fun s : ℝ => MultiBrownian.wAug B s ω j - MultiBrownian.wAug B 0 ω j := by
  refine Continuous.sub ?_ continuous_const
  by_cases h : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
    exact continuous_id
  · simp only [MultiBrownian.wAug, h, ↓reduceDIte]
    exact (B.pathContinuous _ ω).comp continuous_real_toNNReal

/-- **Weierstrass M-test for `⟨ℓ, X_s⟩`.** Under H1, if every level `s ↦ ⟨ℓ_n, X_s^n⟩` is
continuous on `[0, T]` and `‖X_s^n‖ ≤ M n` there with `∑ w n · M n < ∞`, then `s ↦ ⟨ℓ, X_s⟩` is
continuous on `[0, T]`. -/
theorem continuousOn_dualPairing_of_levelNorm_le {T : ℝ} {w : Weight}
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) {X : ℝ → ExtTensorAlgebra (d + 1)}
    (hterm : ∀ n, ContinuousOn (fun s => ℓ.levelInner (X s) n) (Icc 0 T)) {M : ℕ → ℝ}
    (hX : ∀ s ∈ Icc 0 T, ∀ n, (X s).levelNorm n ≤ M n) (hsum : Summable fun n => w n * M n) :
    ContinuousOn (fun s => dualPairing ℓ (X s)) (Icc 0 T) := by
  have hS := hℓ.mem_l2w
  have hnn : ∀ n, 0 ≤ ℓ.levelNormSq n / (w n) ^ 2 := fun n =>
    div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg ℓ n) (sq_nonneg _)
  set C : ℝ := Real.sqrt (∑' n, ℓ.levelNormSq n / (w n) ^ 2) with hC
  have hℓn : ∀ n, ℓ.levelNorm n ≤ C * w n := by
    intro n
    have h1 : ℓ.levelNormSq n / (w n) ^ 2 ≤ ∑' n, ℓ.levelNormSq n / (w n) ^ 2 :=
      hS.le_tsum n fun j _ => hnn j
    have hwpos := w.pos n
    have h2 : ℓ.levelNormSq n ≤ (∑' n, ℓ.levelNormSq n / (w n) ^ 2) * (w n) ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at h1
    calc ℓ.levelNorm n = Real.sqrt (ℓ.levelNormSq n) := rfl
      _ ≤ Real.sqrt ((∑' n, ℓ.levelNormSq n / (w n) ^ 2) * (w n) ^ 2) := Real.sqrt_le_sqrt h2
      _ = C * w n := by
          rw [Real.sqrt_mul (tsum_nonneg hnn), Real.sqrt_sq hwpos.le]
  refine continuousOn_tsum hterm (hsum.mul_left C) fun n s hs => ?_
  calc ‖ℓ.levelInner (X s) n‖ ≤ ℓ.levelNorm n * (X s).levelNorm n :=
        ExtTensorAlgebra.levelInner.abs_le _ _ n
    _ ≤ (C * w n) * M n :=
        mul_le_mul (hℓn n) (hX s hs n) (ExtTensorAlgebra.levelNorm.nonneg _ n)
          (mul_nonneg (Real.sqrt_nonneg _) (w.pos n).le)
    _ = C * (w n * M n) := by ring

/-- **Uniform level majorant of the Brownian signature.** Almost surely there is a deterministic
in `s` majorant `M n ≥ sup_{s ∈ [0,T]} ‖Ŵ_s^{(n)}‖` with `∑ w(n) M n < ∞`, for every admissible
weight `w` (H2). -/
theorem ae_levelNorm_bound_paperSig2 {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) :
    ∀ᵐ ω ∂P, ∃ M : ℕ → ℝ, (∀ s ∈ Icc 0 T, ∀ n, (paperSig2 B 0 s ω).levelNorm n ≤ M n) ∧
      Summable fun n => w n * M n := by
  obtain ⟨r, hr⟩ := hw.le_geometric
  have hr0 : 0 ≤ r := (w.pos 1).le.trans (by simpa using hr 1)
  set K8 : ℝ := (kolSupConst T ^ ((8 : ℝ)⁻¹)).toReal
  have hK80 : 0 ≤ K8 := ENNReal.toReal_nonneg
  have hK8 : kolSupConst T ^ ((8 : ℝ)⁻¹) = ENNReal.ofReal K8 :=
    (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (kolSupConst_ne_top T))).symm
  set c : Word (d + 1) → ℝ → Ω → ℝ := fun I s ω => (paperSig2 B 0 s ω).coeff I
  have hcm : ∀ I s, Measurable (c I s) := fun I s => measurable_paperSig2_coeff B 0 s I
  set S : Word (d + 1) → Ω → ℝ≥0∞ :=
    fun I ω => ⨆ g : gridNN T, ENNReal.ofReal |c I g ω - c I 0 ω|
  set A : ℕ → ℝ := fun n => 1 + n * ((d : ℝ) + 1) ^ n * 2 ^ n
  have hA0 : ∀ n, 0 ≤ A n := fun n => by positivity
  set γ : ℕ → ℝ := fun n => A n * (n * momBound 4 T n)
  set β : ℕ → ℝ := fun n => A n * momBound 4 T n
  have hγ0 : ∀ n, 0 ≤ γ n := fun n => by have := momBound_nonneg 4 T n; positivity
  have hβ0 : ∀ n, 0 ≤ β n := fun n => by have := momBound_nonneg 4 T n; positivity
  have hSm : ∀ I, Measurable (S I) := fun I => by
    have : Countable (gridNN T) := (countable_gridNN T).to_subtype
    exact Measurable.iSup fun g => (((hcm I g).sub (hcm I 0)).abs).ennreal_ofReal
  have hfm : ∀ I, Measurable fun ω => ENNReal.ofReal |c I 0 ω| :=
    fun I => ((hcm I 0).abs).ennreal_ofReal
  -- the grid supremum of each coordinate
  have hS : ∀ n, ∀ I ∈ wordsOfLength (d + 1) n,
      ∫⁻ ω, S I ω ∂P ≤ ENNReal.ofReal (γ n) * ENNReal.ofReal K8 := by
    intro n I hI
    have hIn : I.length = n := wordsOfLength.mem.1 hI
    have h8 := lintegral_iSup_gridNN_le (P := P) (X := c I) (C := γ n ^ 8) hT.le
      (pow_nonneg (hγ0 n) 8) (fun s _ _ => hcm I s) (fun u v hu huv hvT => by
        have hm : MemLp (fun ω => c I v ω - c I u ω) (2 * 4 : ℕ) P :=
          (memLp_paperSig2_coeff B (hu.trans huv) I (by norm_num)).sub
            (memLp_paperSig2_coeff B hu I (by norm_num))
        refine ⟨integrable_pow_of_memLp_evenDeg (N := 2 * 4) ⟨4, rfl⟩ hm, ?_⟩
        have hb := eLpNorm_paperSig2_coeff_sub_le B (q := 4) (by norm_num) hT.le I hu huv hvT
        rw [hIn] at hb
        have hb' : eLpNorm (fun ω => c I v ω - c I u ω) (2 * 4 : ℕ) P ≤
            ENNReal.ofReal (γ n * Real.sqrt (v - u)) := by
          refine hb.trans (le_of_eq ?_)
          congr 1; simp only [γ, A]; ring
        have := integral_pow_le_of_eLpNorm_le (by norm_num) hm
          (mul_nonneg (hγ0 n) (Real.sqrt_nonneg _)) hb'
        refine this.trans (le_of_eq ?_)
        rw [mul_pow, show 2 * 4 = 2 * 4 from rfl, pow_mul (Real.sqrt _),
          Real.sq_sqrt (by linarith)])
    calc ∫⁻ ω, S I ω ∂P
        = ∫⁻ ω, (S I ω ^ (8 : ℝ)) ^ ((1 : ℝ) / 8) * 1 ^ ((7 : ℝ) / 8) ∂P := by
          congr 1; funext ω
          rw [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (∫⁻ ω, S I ω ^ (8 : ℝ) ∂P) ^ ((1 : ℝ) / 8) *
            (∫⁻ _ω, (1 : ℝ≥0∞) ∂P) ^ ((7 : ℝ) / 8) :=
          ENNReal.lintegral_mul_norm_pow_le ((hSm I).pow_const _).aemeasurable aemeasurable_const
            (by norm_num) (by norm_num) (by norm_num)
      _ ≤ (ENNReal.ofReal (γ n ^ 8) * kolSupConst T) ^ ((1 : ℝ) / 8) := by
          simp only [lintegral_const, measure_univ, mul_one, ENNReal.one_rpow]
          exact ENNReal.rpow_le_rpow h8 (by norm_num)
      _ = ENNReal.ofReal (γ n) * ENNReal.ofReal K8 := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← hK8, one_div]
          congr 1
          rw [ENNReal.ofReal_pow (hγ0 n), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
  -- the starting value of each coordinate
  have hC0 : ∀ n, ∀ I ∈ wordsOfLength (d + 1) n,
      ∫⁻ ω, ENNReal.ofReal |c I 0 ω| ∂P ≤ ENNReal.ofReal (β n) := by
    intro n I hI
    have hIn : I.length = n := wordsOfLength.mem.1 hI
    have hb := eLpNorm_paperSig2_coeff_le B (q := 4) (by norm_num) le_rfl I
    rw [hIn] at hb
    calc ∫⁻ ω, ENNReal.ofReal |c I 0 ω| ∂P = eLpNorm (c I 0) 1 P := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          · refine lintegral_congr fun ω => ?_
            rw [Real.enorm_eq_ofReal_abs]
          · exact (hcm I 0).aestronglyMeasurable
      _ ≤ eLpNorm (c I 0) (2 * 4 : ℕ) P :=
          eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ _ := hb
      _ ≤ ENNReal.ofReal (β n) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (momBound_mono 4 hT.le n) (hA0 n))
  -- the random majorant
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (w n) *
    ∑ I ∈ wordsOfLength (d + 1) n, (ENNReal.ofReal |c I 0 ω| + S I ω)
  have hFm : ∀ n, Measurable (F n) := fun n => measurable_const.mul
    (Finset.measurable_sum _ fun I _ => (hfm I).add (hSm I))
  set a : ℕ → ℝ := fun n => r ^ n * (((d : ℝ) + 1) ^ n * (A n * ((n + 1) * momBound 4 T n)))
  have ha0 : ∀ n, 0 ≤ a n := fun n => by have := momBound_nonneg 4 T n; positivity
  have has : Summable a := summable_levelWeight 4 (by norm_num) T hr0
  have hF : ∀ n, ∫⁻ ω, F n ω ∂P ≤ ENNReal.ofReal ((1 + K8) * a n) := by
    intro n
    have hM := momBound_nonneg 4 T n
    have hsumI : ∑ I ∈ wordsOfLength (d + 1) n,
        (∫⁻ ω, ENNReal.ofReal |c I 0 ω| ∂P + ∫⁻ ω, S I ω ∂P) ≤
        ENNReal.ofReal (((d : ℝ) + 1) ^ n * (β n + γ n * K8)) := by
      calc _ ≤ ∑ _I ∈ wordsOfLength (d + 1) n, ENNReal.ofReal (β n + γ n * K8) := by
            refine Finset.sum_le_sum fun I hI => (add_le_add (hC0 n I hI) (hS n I hI)).trans
              (le_of_eq ?_)
            rw [ENNReal.ofReal_add (hβ0 n) (mul_nonneg (hγ0 n) hK80),
              ENNReal.ofReal_mul (hγ0 n)]
        _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_wordsOfLength]
            push_cast; rfl
    calc ∫⁻ ω, F n ω ∂P = ENNReal.ofReal (w n) * ∑ I ∈ wordsOfLength (d + 1) n,
          (∫⁻ ω, ENNReal.ofReal |c I 0 ω| ∂P + ∫⁻ ω, S I ω ∂P) := by
          simp only [F]
          rw [lintegral_const_mul _ (Finset.measurable_sum
              (f := fun I ω => ENNReal.ofReal |c I 0 ω| + S I ω) _ fun I _ => (hfm I).add (hSm I)),
            lintegral_finsetSum (f := fun I ω => ENNReal.ofReal |c I 0 ω| + S I ω) _
              fun I _ => (hfm I).add (hSm I)]
          congr 1
          refine Finset.sum_congr rfl fun I _ => ?_
          exact lintegral_add_left (hfm I) _
      _ ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (((d : ℝ) + 1) ^ n * (β n + γ n * K8)) :=
          mul_le_mul' le_rfl hsumI
      _ = ENNReal.ofReal (w n * (((d : ℝ) + 1) ^ n * (β n + γ n * K8))) :=
          (ENNReal.ofReal_mul (w.pos n).le).symm
      _ ≤ ENNReal.ofReal ((1 + K8) * a n) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : β n ≤ A n * ((n + 1) * momBound 4 T n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (hA0 n)
          have h2 : γ n ≤ A n * ((n + 1) * momBound 4 T n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (hA0 n)
          have h3 : β n + γ n * K8 ≤ (1 + K8) * (A n * ((n + 1) * momBound 4 T n)) := by
            nlinarith
          have h4 : 0 ≤ β n + γ n * K8 := add_nonneg (hβ0 n) (mul_nonneg (hγ0 n) hK80)
          calc w n * (((d : ℝ) + 1) ^ n * (β n + γ n * K8))
              ≤ r ^ n * (((d : ℝ) + 1) ^ n * ((1 + K8) * (A n * ((n + 1) * momBound 4 T n)))) :=
                mul_le_mul (hr n) (mul_le_mul_of_nonneg_left h3 (by positivity))
                  (by positivity) (pow_nonneg hr0 n)
            _ = (1 + K8) * a n := by simp only [a]; ring
  have hΦ : ∫⁻ ω, ∑' n, F n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hFm n).aemeasurable]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, (1 + K8) * a n)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by positivity) (ha0 n))
      (has.mul_left _)]
    exact ENNReal.tsum_le_tsum hF
  have hfin : ∀ᵐ ω ∂P, ∑' n, F n ω < ⊤ := ae_lt_top (Measurable.tsum hFm) hΦ
  filter_upwards [hfin, ae_continuousOn_paperSig2_coeff B hT.le] with ω hΦω hcont
  have hSfin : ∀ n, ∀ I ∈ wordsOfLength (d + 1) n, S I ω ≠ ⊤ := by
    intro n I hI h
    have h1 : F n ω ≤ ∑' n, F n ω := ENNReal.le_tsum (f := fun n => F n ω) n
    have h2 : ∑ J ∈ wordsOfLength (d + 1) n, (ENNReal.ofReal |c J 0 ω| + S J ω) = ⊤ := by
      rw [ENNReal.sum_eq_top]; exact ⟨I, hI, by rw [h]; simp⟩
    have hw0 : ENNReal.ofReal (w n) ≠ 0 := by simpa using w.pos n
    simp only [F, h2, ENNReal.mul_top hw0] at h1
    exact lt_irrefl _ (h1.trans_lt hΦω)
  set M : ℕ → ℝ := fun n => ∑ I ∈ wordsOfLength (d + 1) n, (|c I 0 ω| + (S I ω).toReal)
  have hX : ∀ s ∈ Icc 0 T, ∀ n, (paperSig2 B 0 s ω).levelNorm n ≤ M n := by
    intro s hs n
    refine (levelNorm_le_sum_abs _ n).trans (Finset.sum_le_sum fun I hI => ?_)
    have h1 := ofReal_abs_sub_le_iSup_gridNN hT.le (hcont I) hs
    have h2 : |c I s ω - c I 0 ω| ≤ (S I ω).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hSfin n I hI)).1 h1
    have h3 := abs_add_le (c I 0 ω) (c I s ω - c I 0 ω)
    rw [add_sub_cancel] at h3
    change |c I s ω| ≤ _
    linarith
  have hsum : Summable fun n => w n * M n := by
    refine (ENNReal.summable_toReal hΦω.ne).congr fun n => ?_
    simp only [F]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (w.pos n).le, ENNReal.toReal_sum
      (fun I hI => ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hSfin n I hI⟩)]
    congr 1
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (hSfin n I hI),
      ENNReal.toReal_ofReal (abs_nonneg _)]
  exact ⟨M, hX, hsum⟩

/-- **Almost-sure continuity of `σ = ⟨ℓ, Ŵ⟩`** on `[0, T]` (paper form: the signature
volatility has continuous paths almost surely). Downstream code consumes this form. -/
theorem ae_continuousOn_sigma_of_brownian {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun s => dualPairing ℓ ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω))
      (Icc 0 T) := by
  filter_upwards [ae_levelNorm_bound_paperSig2 B hT w hw, ae_continuousOn_paperSig2_coeff B hT.le]
    with ω hM hcont
  obtain ⟨M, hX, hsum⟩ := hM
  exact continuousOn_dualPairing_of_levelNorm_le hℓ
    (fun n => continuousOn_finsetSum _ fun I _ => continuousOn_const.mul (hcont I)) hX hsum

end SignatureVolatility
