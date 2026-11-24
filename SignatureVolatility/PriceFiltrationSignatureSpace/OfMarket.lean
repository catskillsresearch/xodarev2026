/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.TheoremA

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

/-!
# The price-filtration payoff space `L²(ℱ^S_T, ℚ)` of a market (Section 5, Definition 55)

Everything here is built from the market itself; nothing is assumed abstractly.

* `MarketData`: a signature-volatility model, its Brownian driver, and the analytic hypothesis
  H3 under which Theorem A constructs the price.
* `MarketData.S`: the Theorem A signature price. It is a `ℙ`-martingale
  (`SignaturePriceSolution.is_martingale`), so `ℚ = ℙ`.
* `MarketData.F_ST`: the price σ-algebra `ℱ^S_T = σ(S_u : 0 ≤ u ≤ T)`.
* `MarketData.L2S`: `L²(ℱ^S_T, ℚ)`, the closed subspace `lpMeas` of `L²(ℙ)`.
* `MarketData.coord I`: the terminal signature coordinate `⟨e_I, Ŵ_T⟩ ∈ L²(ℙ)` (Prop. 12).
* `MarketData.sigSpan N`: the paper's Definition 55 space
  `closure span_{L²(ℚ)} {⟨e_I, Ŵ_T⟩ : |I| ≤ N} ∩ L²(ℱ^S_T, ℚ)`.
* `MarketData.completenessDepth`: `N^*_S`, the least `N` with `sigSpan N = L²(ℱ^S_T, ℚ)`, or `⊤`.

**Main fact.** `sigSpan N` is finite-dimensional, because it lies in the span of finitely many
vectors. So `N^*_S < ∞` forces `L²(ℱ^S_T, ℚ)` to be finite-dimensional.
`completenessDepth_eq_top_of_not_finiteDimensional` proves that `N^*_S = ∞` whenever
`L²(ℱ^S_T, ℚ)` is infinite-dimensional, which is every non-degenerate model.
`not_finiteDimensional_lpMeas_of_disjoint` gives a convenient sufficient condition:
infinitely many disjoint price events of positive probability.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Market data for Theorems C–D: the model, its Brownian driver, and the analytic H3 hypothesis
of Theorem A, which constructs the signature price `S`. -/
structure MarketData (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    where
  M : SignatureVolatilityModel
  B : MultiBrownian Ω P M.d
  h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))

namespace MarketData

/-- Paper-strength prolonged setup for this market. -/
abbrev setup (mkt : MarketData Ω P) :=
  paperSetup mkt.B mkt.M.hT

/-- The Theorem A signature-price solution of the market. -/
def sol (mkt : MarketData Ω P) :
    SignaturePriceSolution mkt.M (paperSetup mkt.B mkt.M.hT)
      (itoCalculusKit_of_mathfin mkt.B mkt.M.hT) :=
  (theorem_A mkt.M mkt.B mkt.h3).choose

/-- The signature price `S`. -/
def S (mkt : MarketData Ω P) : ℝ → Ω → ℝ := mkt.sol.S

/-- The price filtration `ℱ^S_t = σ(S_u : 0 ≤ u ≤ t)`. -/
def F_S (mkt : MarketData Ω P) : IndexedFiltration Ω :=
  priceFiltration mkt.S mkt.sol.S_meas

/-- The terminal price σ-algebra `ℱ^S_T`. -/
abbrev F_ST (mkt : MarketData Ω P) : MeasurableSpace Ω := mkt.F_S.σAlg mkt.M.T

lemma F_ST_le (mkt : MarketData Ω P) : mkt.F_ST ≤ ‹MeasurableSpace Ω› :=
  mkt.F_S.le_ambient _

/-- `S_t` is `ℱ^S_T`-measurable for `0 ≤ t ≤ T`. -/
lemma measurable_S (mkt : MarketData Ω P) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ mkt.M.T) :
    Measurable[mkt.F_ST] (mkt.S t) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun (s : {s : ℝ // 0 ≤ s ∧ s ≤ mkt.M.T}) (_ : Unit) =>
    MeasurableSpace.comap (mkt.S s.1) inferInstance) ⟨t, ht0, htT⟩ () le_rfl

/-- `L²(ℱ^S_T, ℚ)` (with `ℚ = ℙ`) as a closed subspace of `L²(ℙ)`. -/
abbrev L2S (mkt : MarketData Ω P) : Submodule ℝ (Lp ℝ 2 P) :=
  lpMeas ℝ ℝ mkt.F_ST 2 P

lemma memLp_coord (mkt : MarketData Ω P) (I : Word (mkt.M.d + 1)) :
    MemLp (fun ω => (mkt.setup.W_hat mkt.M.T ω).coeff I) 2 P := by
  have h := memLp_paperSig2_coeff mkt.B mkt.M.hT.le I (q := 2) le_rfl
  exact h.mono_exponent (by norm_num)

/-- The terminal signature coordinate `⟨e_I, Ŵ_T⟩` as an element of `L²(ℙ)`. -/
def coord (mkt : MarketData Ω P) (I : Word (mkt.M.d + 1)) : Lp ℝ 2 P :=
  (mkt.memLp_coord I).toLp _

/-- The depth-`≤ N` coordinates `{⟨e_I, Ŵ_T⟩ : |I| ≤ N}`. -/
def coordSet (mkt : MarketData Ω P) (N : ℕ) : Set (Lp ℝ 2 P) :=
  {f | ∃ I : Word (mkt.M.d + 1), I.length ≤ N ∧ f = mkt.coord I}

/-- **Definition 55 space.**
`closure span_{L²(ℚ)} {⟨e_I, Ŵ_T⟩ : |I| ≤ N} ∩ L²(ℱ^S_T, ℚ)`. -/
def sigSpan (mkt : MarketData Ω P) (N : ℕ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (mkt.coordSet N)).topologicalClosure ⊓ mkt.L2S

/-- **Definition 55.** The price-filtration completeness depth `N^*_S`: the least `N` with
`sigSpan N = L²(ℱ^S_T, ℚ)`, and `⊤` if there is none. -/
def completenessDepth (mkt : MarketData Ω P) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ n : ℕ, K = (n : ℕ∞) ∧ mkt.sigSpan n = mkt.L2S}

lemma coordSet_finite (mkt : MarketData Ω P) (N : ℕ) : (mkt.coordSet N).Finite := by
  classical
  let W : Finset (Word (mkt.M.d + 1)) :=
    (Finset.range (N + 1)).biUnion (wordsOfLength (mkt.M.d + 1))
  refine (W.finite_toSet.image mkt.coord).subset ?_
  rintro f ⟨I, hI, rfl⟩
  refine ⟨I, ?_, rfl⟩
  simp only [W, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.mem_coe,
    wordsOfLength.mem, Set.mem_Iio]
  exact ⟨I.length, Nat.lt_succ_of_le hI, rfl⟩

instance finiteDimensional_span_coordSet (mkt : MarketData Ω P) (N : ℕ) :
    FiniteDimensional ℝ (Submodule.span ℝ (mkt.coordSet N)) :=
  FiniteDimensional.span_of_finite ℝ (mkt.coordSet_finite N)

/-- `sigSpan N` lies in a finite-dimensional subspace. -/
lemma sigSpan_le_span (mkt : MarketData Ω P) (N : ℕ) :
    mkt.sigSpan N ≤ Submodule.span ℝ (mkt.coordSet N) := by
  rw [sigSpan, Submodule.topologicalClosure_eq_self]
  exact inf_le_left

instance finiteDimensional_sigSpan (mkt : MarketData Ω P) (N : ℕ) :
    FiniteDimensional ℝ (mkt.sigSpan N) :=
  Submodule.finiteDimensional_of_le (mkt.sigSpan_le_span N)

/-- `sigSpan N` is closed. So "dense in `L²(ℱ^S_T)`" (the paper's Theorem C wording) and
"equal to `L²(ℱ^S_T)`" (Definition 55) are the same condition. -/
lemma topologicalClosure_sigSpan (mkt : MarketData Ω P) (N : ℕ) :
    (mkt.sigSpan N).topologicalClosure = mkt.sigSpan N :=
  Submodule.topologicalClosure_eq_self _

/-- If `L²(ℱ^S_T, ℚ)` is infinite-dimensional, no finite-depth signature span (closed or not)
fills it. -/
theorem sigSpan_ne_L2S_of_not_finiteDimensional (mkt : MarketData Ω P)
    (hinf : ¬ FiniteDimensional ℝ mkt.L2S) (N : ℕ) :
    (mkt.sigSpan N).topologicalClosure ≠ mkt.L2S := by
  intro h
  rw [topologicalClosure_sigSpan] at h
  apply hinf
  rw [← h]
  infer_instance

/-- **Definition 55 gives `N^*_S = ∞` in every non-degenerate model.** If `L²(ℱ^S_T, ℚ)` is
infinite-dimensional, the completeness depth is `⊤`. -/
theorem completenessDepth_eq_top_of_not_finiteDimensional (mkt : MarketData Ω P)
    (hinf : ¬ FiniteDimensional ℝ mkt.L2S) : mkt.completenessDepth = ⊤ := by
  rw [completenessDepth, sInf_eq_top]
  rintro K ⟨n, -, hn⟩
  exact absurd (by rw [topologicalClosure_sigSpan]; exact hn)
    (mkt.sigSpan_ne_L2S_of_not_finiteDimensional hinf n)

end MarketData

/-- **Sufficient condition for infinite dimension.** If a sub-σ-algebra `m` has infinitely many
pairwise disjoint events of positive probability, then `L²(m, ℙ)` is infinite-dimensional. -/
theorem not_finiteDimensional_lpMeas_of_disjoint {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ m0) (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet[m] (A k))
    (hpos : ∀ k, P (A k) ≠ 0) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ¬ FiniteDimensional ℝ (lpMeas ℝ ℝ m 2 P) := by
  intro hfin
  let f : ℕ → Lp ℝ 2 P := fun k =>
    indicatorConstLp 2 (hm _ (hA k)) (measure_ne_top P (A k)) (1 : ℝ)
  have hf_mem : ∀ k, f k ∈ lpMeas ℝ ℝ m 2 P := fun k =>
    mem_lpMeas_indicatorConstLp hm (hA k) (measure_ne_top P (A k))
  have hne : ∀ k, f k ≠ 0 := by
    intro k hk
    have hn := norm_indicatorConstLp (p := (2 : ENNReal)) (μ := P) (c := (1 : ℝ))
      (hs := hm _ (hA k)) (hμs := measure_ne_top P (A k)) (by norm_num) (by norm_num)
    have hk' : ‖f k‖ = 0 := by rw [hk, norm_zero]
    rw [hk'] at hn
    have hreal : 0 < P.real (A k) :=
      ENNReal.toReal_pos (hpos k) (measure_ne_top P (A k))
    have : 0 < ‖(1 : ℝ)‖ * P.real (A k) ^ (1 / (2 : ENNReal).toReal) := by
      rw [norm_one, one_mul]; exact Real.rpow_pos_of_pos hreal _
    linarith
  have horth : Pairwise fun i j => (inner ℝ (f i) (f j) : ℝ) = 0 := by
    intro i j hij
    simp only [f]
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
    have hzero : ∀ᵐ x ∂(P.restrict (A i)),
        (inner ℝ (1 : ℝ)
          ((indicatorConstLp 2 (hm _ (hA j)) (measure_ne_top P (A j)) (1 : ℝ) : Lp ℝ 2 P) x) :
          ℝ) = 0 := by
      have hco := (indicatorConstLp_coeFn (p := (2 : ENNReal)) (μ := P)
        (hs := hm _ (hA j)) (hμs := measure_ne_top P (A j)) (c := (1 : ℝ)))
      have hco' := ae_restrict_of_ae (s := A i) hco
      filter_upwards [hco', ae_restrict_mem (hm _ (hA i))] with x hx hxi
      have hxj : x ∉ A j := fun hxj => Set.disjoint_left.mp (hdisj hij) hxi hxj
      rw [hx, Set.indicator_of_notMem hxj]
      simp
    rw [integral_congr_ae hzero, integral_zero]
  have hli : LinearIndependent ℝ f := linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  let g : ℕ → lpMeas ℝ ℝ m 2 P := fun k => ⟨f k, hf_mem k⟩
  have hg : LinearIndependent ℝ g :=
    LinearIndependent.of_comp (lpMeas ℝ ℝ m 2 P).subtype hli
  have := hg.finite
  exact not_finite ℕ

end SignatureVolatility
