module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.ProlongedBrownianSetup.WHat


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Pathwise continuity of the signature volatility

For the Stratonovich (chordal) setup over a continuous driver, `σ_s(ω) = ⟨ℓ, Ŵ_s(ω)⟩` is
continuous on `[0, T]` for every `ω` under H1–H2 (`continuousOn_sigma_of_brownian`).
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

/-- **Pathwise continuity of `σ = ⟨ℓ, Ŵ⟩`** on `[0, T]` for the Stratonovich setup over a
continuous driver, under H1–H2 (Weierstrass M-test on the level series). -/
theorem continuousOn_sigma_of_brownian {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) (ω : Ω) :
    ContinuousOn
      (fun s => dualPairing ℓ ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω))
      (Icc 0 T) := by
  have hxc := continuous_wAug_sub B ω
  have hWhat : ∀ s, (prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω =
      ExtTensorAlgebra.tensorExp
        (fun j => MultiBrownian.wAug B s ω j - MultiBrownian.wAug B 0 ω j) :=
    fun s => sig2OfBrownian_zero_left B s ω
  have hnorm : ∀ s n, ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω).levelNorm n =
      incrNorm B s ω ^ n / (n.factorial : ℝ) := fun s n => sig2OfBrownian_levelNorm_eq B s ω n
  -- each level is continuous
  have hterm : ∀ n, Continuous fun s =>
      ℓ.levelInner ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω) n := by
    intro n
    simp only [hWhat, ExtTensorAlgebra.levelInner, ExtTensorAlgebra.tensorExp]
    refine continuous_finsetSum _ fun I _ => continuous_const.mul ?_
    exact (continuous_list_prod I fun j _ => hxc j).div_const _
  -- uniform bound on the increment norm over `[0, T]`
  have hincr : Continuous fun s => incrNorm B s ω := by
    unfold incrNorm
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ => (hxc j).pow 2)
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hincr.continuousOn
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ s ∈ Icc 0 T, incrNorm B s ω ≤ R := fun s hs =>
    (hR₀ (mem_image_of_mem _ hs)).trans (le_max_left _ _)
  -- H1 gives `‖ℓ_n‖ ≤ C · w n`
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
  -- M-test
  have hsum : Summable fun n : ℕ => C * (w n * (R ^ n / (n.factorial : ℝ))) :=
    (hw.subfactorial_nonneg (le_max_right _ _)).mul_left C
  refine continuousOn_tsum (fun n => (hterm n).continuousOn) hsum fun n s hs => ?_
  have hi0 := incrNorm_nonneg B s ω
  calc ‖ℓ.levelInner ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω) n‖
      ≤ ℓ.levelNorm n *
          ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω).levelNorm n :=
        ExtTensorAlgebra.levelInner.abs_le _ _ n
    _ = ℓ.levelNorm n * (incrNorm B s ω ^ n / (n.factorial : ℝ)) := by rw [hnorm]
    _ ≤ (C * w n) * (R ^ n / (n.factorial : ℝ)) := by
        refine mul_le_mul (hℓn n) ?_ (by positivity) (by have := w.pos n; positivity)
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hi0 (hR s hs) n) (Nat.cast_nonneg _)
    _ = C * (w n * (R ^ n / (n.factorial : ℝ))) := by ring

end SignatureVolatility
