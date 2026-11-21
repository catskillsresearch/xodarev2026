module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.Concat
public import SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.GeneratedFiltration
public import SignatureVolatility.IndexedFiltration


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

structure ProlongedBrownianSetup (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (d : ℕ) (T : ℝ) where
  hT_pos : 0 < T
  /-- `d`-dimensional standard Brownian motion `W_t(ω)`. -/
  W : ℝ → Ω → Fin d → ℝ
  W_zero : ∀ ω i, W 0 ω i = 0
  W_meas : ∀ t i, Measurable (fun ω => W t ω i)
  /-- Two-parameter Stratonovich signature `Ŵ_{s, t}(ω) ∈ T((ℝ^{d+1}))`. -/
  sig2 : ℝ → ℝ → Ω → ExtTensorAlgebra (d + 1)
  sig_meas : ∀ s t I, Measurable (fun ω => (sig2 s t ω).coeff I)
  /-- Empty word coordinate is `1`. -/
  sig2_empty : ∀ s t ω, (sig2 s t ω).coeff [] = 1
  /-- Level-1 time coordinate `⟨e_{(0)}, Ŵ_{s,t}⟩ = t - s`. -/
  sig2_time : ∀ s t ω, (sig2 s t ω).coeff [0] = t - s
  /-- Level-1 Brownian coordinate `⟨e_{(i+1)}, Ŵ_{s,t}⟩ = W^i_t - W^i_s`. -/
  sig2_space : ∀ s t ω (i : Fin d), (sig2 s t ω).coeff [i.succ] = W t ω i - W s ω i
  /-- Stratonovich signature of `(t, W_t)` up to time `s` is measurable w.r.t. the path of `W`
  up to time `s`. -/
  sig_adapted_to_W : ∀ (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (I : Word (d + 1)),
    Measurable[(generatedFiltration (fun u i ω => W u ω i) W_meas).σAlg t]
      (fun ω => (sig2 0 s.1 ω).coeff I)
  /-- Multiplicative rough-path/Stratonovich simplex decomposition over `[0, s] ∪ [s, t]`. -/
  stratonovich_chen : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    ∀ ω, sig2 0 t ω = sig2 0 s ω ⊗ₜ sig2 s t ω
  /-- Product-of-simplices Stratonovich shuffle relation on coordinates. -/
  stratonovich_shuffle : ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    ∀ (I J : Word (d + 1)) (ω : Ω),
      (sig2 0 t ω).coeff I * (sig2 0 t ω).coeff J =
        ExtTensorAlgebra.evalShuffleBasis I J (sig2 0 t ω)
  /-- Appendix A / paper Proposition 12 factorial level control: for each `p ≥ 1` and any
  nonnegative weight sequence of at most geometric growth `w_n ≤ r^n` (as supplied by `HypH2`
  via submultiplicativity), the weighted level series of `sig2 0 t` converges pathwise and
  lies in `L^p`. Weaker all-radius `R^n/n!` summability is insufficient for Gaussian drivers. -/
  factorial_moment_control : ∀ (p : ℝ), 1 ≤ p →
    ∀ (w_fn : ℕ → ℝ), (∀ n, 0 ≤ w_fn n) →
      (∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n) →
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
        (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2 0 t ω).levelNorm n)) ∧
        Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p) ℙ

end SignatureVolatility
