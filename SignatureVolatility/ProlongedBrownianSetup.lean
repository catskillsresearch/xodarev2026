module

public import SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.GeneratedFiltration


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-- Coordinate `j` of the time-extended path `X_t = (t, W_t)`: `X⁰_t = t`, `X^{i+1}_t = W^i_t`. -/
def augCoord {Ω : Type*} {d : ℕ} (W : ℝ → Ω → Fin d → ℝ) (t : ℝ) (ω : Ω) (j : Fin (d + 1)) :
    ℝ :=
  Fin.cases (motive := fun _ => ℝ) t (fun i => W t ω i) j

/-- Trapezoid (Stratonovich) Riemann sum `∑ₖ ½ (Y_{t_k} + Y_{t_{k+1}}) (X^j_{t_{k+1}} - X^j_{t_k})`
on the uniform grid `t_k = k t / (n + 1)`, `k = 0, …, n`. -/
def trapezoidSum {Ω : Type*} {d : ℕ} (W : ℝ → Ω → Fin d → ℝ) (Y : ℝ → Ω → ℝ)
    (j : Fin (d + 1)) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (1 / 2 : ℝ) * (Y (k * t / (n + 1)) ω + Y ((k + 1) * t / (n + 1)) ω) *
      (augCoord W ((k + 1) * t / (n + 1)) ω j - augCoord W (k * t / (n + 1)) ω j)

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
  /-- Multiplicative rough-path/Stratonovich simplex decomposition over `[0, s] ∪ [s, t]`
  (almost surely: iterated stochastic integrals are only defined up to null sets). -/
  stratonovich_chen : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    ∀ᵐ ω ∂ℙ, sig2 0 t ω = sig2 0 s ω ⊗ₜ sig2 s t ω
  /-- Product-of-simplices Stratonovich shuffle relation on coordinates (almost surely). -/
  stratonovich_shuffle : ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    ∀ (I J : Word (d + 1)), ∀ᵐ ω ∂ℙ,
      (sig2 0 t ω).coeff I * (sig2 0 t ω).coeff J =
        ExtTensorAlgebra.evalShuffleBasis I J (sig2 0 t ω)
  /-- Paper's defining dynamics `dŴ_t = Ŵ_t ⊗ ∘dX_t` (last letter latest): coordinatewise,
  `⟨e_{Ij}, Ŵ_t⟩ = ∫₀ᵗ ⟨e_I, Ŵ_s⟩ ∘dX^j_s`, the Stratonovich integral being the limit in
  probability of trapezoid sums on uniform grids. This pins `sig2` to the signature of
  `X = (t, W_t)`. -/
  stratonovich_dynamics : ∀ (I : Word (d + 1)) (j : Fin (d + 1)) ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    TendstoInMeasure ℙ (fun n => trapezoidSum W (fun s ω => (sig2 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (sig2 0 t ω).coeff (I ++ [j]))
  /-- Appendix A / paper Proposition 12 factorial level control: for each `p ≥ 1` and any
  nonnegative weight sequence of at most geometric growth `w_n ≤ r^n` (as supplied by `HypH2`
  via submultiplicativity), the weighted level series of `sig2 0 t` converges almost surely and
  lies in `L^p`. Weaker all-radius `R^n/n!` summability is insufficient for Gaussian drivers. -/
  factorial_moment_control : ∀ (p : ℝ), 1 ≤ p →
    ∀ (w_fn : ℕ → ℝ), (∀ n, 0 ≤ w_fn n) →
      (∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n) →
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
        (∀ᵐ ω ∂ℙ, Summable (fun n : ℕ => w_fn n * (sig2 0 t ω).levelNorm n)) ∧
        Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p) ℙ

end SignatureVolatility
