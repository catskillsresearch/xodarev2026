/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.Prop58BlackScholesDepthFalse
public import MathFin.Probability.Brownian.MartingaleRepresentation

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathFin MathFin.ItoIntegralCLM MathFin.ItoIntegralL2
open scoped NNReal

namespace SignatureVolatility

/-!
# CounterExample_TheoremC: Black–Scholes refutes the unconditional completeness equivalence

Theorem 56 restricts "complete with finitely many calls ⇔ `N^*_S < ∞`" to the finite-polynomial
subcase `K(N^*_S) < ∞` and a sufficiently rich strike set. The **unconditional** form of that
equivalence — for an arbitrary finite strike set, with no `K(N^*_S) < ∞` hypothesis — is false
for Black–Scholes, and so is the paper's separate claim that Black–Scholes has `N^*_S = 0`:

* `blackScholes_isCompleteWithCalls`: every `X ∈ L²(ℱ^S_T)` is `E X` plus a stochastic integral
  (Brownian martingale representation, vendored `MathFin.exists_itoIntegral_representation`),
  so the market is complete, for every finite strike set (no calls are even needed);
* `blackScholes_completenessDepth_eq_top`: under Definition 55, `N^*_S = ∞`.

Hence `not_theorem_C`: `¬ (complete ↔ N^*_S < ∞)`. This is not a counterexample inside
Theorem 56's stated subcase, because the Black–Scholes witness has `N^*_S = ∞`.

**Strategies.** In Black–Scholes `dS = σ₀ S dW`, so `∫ H dS = ∫ (σ₀ H S) dW`, and
`H ↦ φ = σ₀ H S` is a bijection (`S > 0`, `σ₀ ≠ 0`) between price-integrands and Brownian
integrands. Completeness is therefore stated with gains `itoIntegralCLM φ`, `φ` square-integrable
and predictable for the Brownian filtration on `[0, T]`. That filtration *is* the price filtration:
`blackScholes_priceFiltration_eq` shows `ℱ^S_t = ℱ^W_t` for every `t ≥ 0`, so these are exactly
the admissible price-predictable strategies.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)

/-- The Brownian driver of the one-dimensional market. -/
def bsDriver (B : MultiBrownian Ω P 1) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B.Wnn t ω (kitDriver Nat.one_pos)

lemma bsDriver_meas (B : MultiBrownian Ω P 1) : ∀ t, Measurable (bsDriver B t) :=
  fun t => B.Wnn_meas t _

lemma bsDriver_cont (B : MultiBrownian Ω P 1) : ∀ ω, Continuous fun t => bsDriver B t ω :=
  fun ω => B.pathContinuous _ ω

lemma bsDriver_isPreBrownian (B : MultiBrownian Ω P 1) : IsPreBrownianReal (bsDriver B) P :=
  (B.isBrownian (kitDriver Nat.one_pos)).toIsPreBrownianReal

/-- The Black–Scholes price is geometric Brownian motion at every time `s ≥ 0` and every `ω`. -/
lemma blackScholesMarket_S (B : MultiBrownian Ω P 1) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).S s ω =
      s₀ * Real.exp (σ₀ * B.Wnn (Real.toNNReal s) ω (kitDriver Nat.one_pos) -
        (1 / 2 : ℝ) * (σ₀ ^ 2 * s)) := by
  have h := (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).sol.doleans_repr s ω
  have hσ : SignatureVolatilityModel.sigma (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).M
      (paperSetup (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).B
        (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).M.hT) = fun _ _ => σ₀ :=
    sigma_blackScholes T s₀ σ₀ hT hs₀ hσ₀ B
  rw [hσ] at h
  have h1 := kitItoInt_const B Nat.one_pos σ₀ hs ω
  have h2 := kitQuadVar_const B Nat.one_pos σ₀ hs ω
  change _ = s₀ * Real.exp (kitItoInt B (fun _ _ => σ₀) s ω -
    (1 / 2 : ℝ) * kitQuadVar B (fun _ _ => σ₀) s ω) at h
  rw [h1, h2] at h
  exact h

/-- `ℱ^S_t ≤ ℱ^W_t`. -/
lemma blackScholes_priceFiltration_le (B : MultiBrownian Ω P 1) (t : ℝ) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).F_S.σAlg t ≤
      natFiltration (bsDriver_meas B) (Real.toNNReal t) := by
  set mkt := blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B
  change (⨆ (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (_ : Unit),
    MeasurableSpace.comap (mkt.S s.1) inferInstance) ≤ _
  refine iSup₂_le fun s _ => ?_
  rw [← measurable_iff_comap_le]
  have hW : Measurable[natFiltration (bsDriver_meas B) (Real.toNNReal t)]
      (bsDriver B (Real.toNNReal s.1)) :=
    ((stronglyAdapted_natFiltration (bsDriver_meas B) (Real.toNNReal s.1)).measurable).mono
      ((natFiltration (bsDriver_meas B)).mono
        (Real.toNNReal_le_toNNReal s.2.2)) le_rfl
  have heq : mkt.S s.1 = fun ω => s₀ * Real.exp (σ₀ * bsDriver B (Real.toNNReal s.1) ω -
      (1 / 2 : ℝ) * (σ₀ ^ 2 * s.1)) := by
    funext ω; exact blackScholesMarket_S T s₀ σ₀ hT hs₀ hσ₀ B s.2.1 ω
  rw [heq]
  exact measurable_const.mul (((measurable_const.mul hW).sub_const _).exp)

/-- `ℱ^W_t ≤ ℱ^S_t` (for `t ≥ 0`). -/
lemma blackScholes_le_priceFiltration (B : MultiBrownian Ω P 1) {t : ℝ} (ht : 0 ≤ t) :
    natFiltration (bsDriver_meas B) (Real.toNNReal t) ≤
      (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).F_S.σAlg t := by
  set mkt := blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B
  change (⨆ j ≤ Real.toNNReal t, MeasurableSpace.comap (bsDriver B j) inferInstance) ≤ _
  refine iSup₂_le fun j hj => ?_
  rw [← measurable_iff_comap_le]
  have hjt : (j : ℝ) ≤ t := (Real.le_toNNReal_iff_coe_le ht).mp hj
  have hS : Measurable[mkt.F_S.σAlg t] (mkt.S (j : ℝ)) := by
    rw [measurable_iff_comap_le]
    exact le_iSup₂_of_le (f := fun (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (_ : Unit) =>
      MeasurableSpace.comap (mkt.S s.1) inferInstance) ⟨j, j.2, hjt⟩ () le_rfl
  have heq : bsDriver B j =
      fun ω => (Real.log (mkt.S (j : ℝ) ω / s₀) + (1 / 2 : ℝ) * (σ₀ ^ 2 * j)) / σ₀ := by
    funext ω
    have hSj : mkt.S (j : ℝ) ω = s₀ * Real.exp (σ₀ * B.Wnn (Real.toNNReal (j : ℝ)) ω
        (kitDriver Nat.one_pos) - (1 / 2 : ℝ) * (σ₀ ^ 2 * j)) :=
      blackScholesMarket_S T s₀ σ₀ hT hs₀ hσ₀ B j.2 ω
    rw [hSj, mul_div_cancel_left₀ _ hs₀.ne',
      Real.log_exp, Real.toNNReal_coe]
    unfold bsDriver
    field_simp
    ring
  rw [heq]
  exact (((hS.div_const s₀).log).add_const _).div_const σ₀

/-- In Black–Scholes the price filtration equals the Brownian filtration: `ℱ^S_t = ℱ^W_t`. -/
theorem blackScholes_priceFiltration_eq (B : MultiBrownian Ω P 1) {t : ℝ} (ht : 0 ≤ t) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).F_S.σAlg t =
      natFiltration (bsDriver_meas B) (Real.toNNReal t) :=
  le_antisymm (blackScholes_priceFiltration_le T s₀ σ₀ hT hs₀ hσ₀ B t)
    (blackScholes_le_priceFiltration T s₀ σ₀ hT hs₀ hσ₀ B ht)

/-- **Completeness with finitely many calls** (unconditional equivalence, left-hand side), for the
Black–Scholes market: every claim `X ∈ L²(ℱ^S_T)` is replicated by a cash position `c`, static
call positions `a k` at the strikes, and a dynamic strategy with gains `∫ φ dW = ∫ H dS`
(`φ = σ₀ H S`; see the module docstring). -/
def IsCompleteWithCalls (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) : Prop :=
  ∀ X : Lp ℝ 2 P, X ∈ (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).L2S →
    ∃ (c : ℝ) (a : ℝ → ℝ)
      (φ : Lp ℝ 2 (trimMeasure (μ := P) (Real.toNNReal T) (bsDriver_meas B))),
      (X : Ω → ℝ) =ᵐ[P] fun ω => c +
        ∑ k ∈ strikes, a k * max ((blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).S T ω - k) 0 +
        itoIntegralCLM (bsDriver_isPreBrownian B) (Real.toNNReal T) (bsDriver_meas B) φ ω

/-- Black–Scholes is complete on `ℱ^S_T`, for every finite set of strikes. -/
theorem blackScholes_isCompleteWithCalls (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    IsCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes := by
  intro X hX
  have hXm := mem_lpMeas_iff_aestronglyMeasurable.mp hX
  have hle := blackScholes_priceFiltration_le T s₀ σ₀ hT hs₀ hσ₀ B T
  obtain ⟨g, hg, hfg⟩ := hXm
  have hXW : AEStronglyMeasurable[natFiltration (bsDriver_meas B) (Real.toNNReal T)]
      (X : Ω → ℝ) P := ⟨g, hg.mono hle, hfg⟩
  obtain ⟨φ, hφ, -⟩ := exists_itoIntegral_representation (bsDriver_isPreBrownian B)
    (bsDriver_meas B) (bsDriver_cont B) (Real.toNNReal T) X hXW
  refine ⟨∫ x, X x ∂P, 0, φ, hφ.trans (Filter.Eventually.of_forall fun ω => ?_)⟩
  simp

/-- **Unconditional completeness iff and Black–Scholes depth.** For the Black–Scholes market and any
finite set of call strikes, the unconditional equivalence "complete on `ℱ^S_T` ⇔ `N^*_S < ∞`" is
false: the market is complete, but Definition 55 gives `N^*_S = ∞`. This also refutes the paper's
separate Black–Scholes depth claim (`N^*_S = 0`). It is not a counterexample inside Theorem 56's
finite-polynomial subcase `K(N^*_S) < ∞` with a sufficiently rich strike set. -/
theorem not_theorem_C (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    ¬ (IsCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes ↔
      (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤) := by
  intro h
  have := h.mp (blackScholes_isCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes)
  rw [blackScholes_completenessDepth_eq_top] at this
  exact lt_irrefl _ this

end SignatureVolatility
