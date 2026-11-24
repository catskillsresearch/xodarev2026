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

/-- **Almost-sure continuity of `σ = ⟨ℓ, Ŵ⟩`** on `[0, T]` (paper form: the signature
volatility has continuous paths almost surely). Downstream code consumes this form. -/
theorem ae_continuousOn_sigma_of_brownian {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun s => dualPairing ℓ ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s ω))
      (Icc 0 T) := by
  sorry

end SignatureVolatility
