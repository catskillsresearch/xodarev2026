/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.PriceFiltrationSignatureSpace.OfMarket

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace SignatureVolatility

/-!
# The Galtchouk–Kunita–Watanabe projection on `L²(ℱ^S_T, ℚ)` (Definition 65, Theorem 66)

Everything is built from the market (`MarketData`), with `ℚ = ℙ`, since the Theorem A price is a
`ℙ`-martingale.

* `gainsSet`: the square-integrable stochastic integrals `∫_0^T H_s dS_s = ∫_0^T H_s S_s σ_s dB_s`
  in `L²(ℱ^S_T)`, with `H` adapted to the price filtration.
* `H0`: Definition 65's "closed subspace of constants and square-integrable stochastic integrals
  against `S`", that is, the closed span of `1` and `gainsSet`.
* `gkw_decomposition`: for every `X ∈ L²(ℱ^S_T)` there are unique `G` and `ε` with
  `X = E[X] + G + ε`, where `G ∈ H0`, `E[G] = 0`, `ε ∈ L²(ℱ^S_T)` and `ε ⊥ H0`
  (in particular `ε` is orthogonal to every stochastic integral against `S`), and
  `‖X‖² = ‖E[X] + G‖² + ‖ε‖²`.

Theorem 66 also says that `G` is a single stochastic integral `∫ H^X dS`. That needs the gains
space to be closed (Itô isometry together with the Kunita–Watanabe argument), which is not
formalised here. What is proved here is that `G` lies in the closed span `H0`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace MarketData

/-- The constant payoff `1 ∈ L²(ℙ)`. -/
def oneLp (P : Measure Ω) [IsProbabilityMeasure P] : Lp ℝ 2 P :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)

lemma inner_oneLp (f : Lp ℝ 2 P) : ⟪oneLp P, f⟫ = ∫ ω, f ω ∂P := by
  rw [oneLp, L2.inner_indicatorConstLp_eq_setIntegral_inner, Measure.restrict_univ]
  simp

lemma inner_oneLp_oneLp : ⟪oneLp P, oneLp P⟫ = 1 := by
  rw [inner_oneLp, oneLp, integral_indicatorConstLp]
  simp

lemma oneLp_mem_L2S (mkt : MarketData Ω P) : oneLp P ∈ mkt.L2S :=
  mem_lpMeas_indicatorConstLp mkt.F_ST_le MeasurableSet.univ (measure_ne_top P univ)

/-- Square-integrable stochastic integrals against `S`:
`∫_0^T H_s dS_s = ∫_0^T H_s S_s σ_s dB_s` with `H` adapted to `ℱ^S`, lying in `L²(ℱ^S_T)`. -/
def gainsSet (mkt : MarketData Ω P) : Set (Lp ℝ 2 P) :=
  {X | X ∈ mkt.L2S ∧ ∃ H : ℝ → Ω → ℝ, (∀ t, Measurable[mkt.F_S.σAlg t] (H t)) ∧
    (X : Ω → ℝ) =ᵐ[P] (itoCalculusKit_of_mathfin mkt.B mkt.M.hT).itoInt
      (fun s ω => H s ω * mkt.S s ω * SignatureVolatilityModel.sigma mkt.M mkt.setup s ω)
      mkt.M.T}

/-- **Definition 65.** `H0`, the closed subspace of constants and square-integrable stochastic
integrals against `S`. -/
def H0 (mkt : MarketData Ω P) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (insert (oneLp P) mkt.gainsSet)).topologicalClosure

instance completeSpace_H0 (mkt : MarketData Ω P) : CompleteSpace mkt.H0 :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance hasOrthogonalProjection_H0 (mkt : MarketData Ω P) :
    mkt.H0.HasOrthogonalProjection := inferInstance

lemma isClosed_L2S (mkt : MarketData Ω P) : IsClosed (mkt.L2S : Set (Lp ℝ 2 P)) := by
  have : (mkt.L2S : Set (Lp ℝ 2 P)) =
      {f : Lp ℝ 2 P | AEStronglyMeasurable[mkt.F_ST] f P} := by
    ext f; exact mem_lpMeas_iff_aestronglyMeasurable
  rw [this]
  exact isClosed_aestronglyMeasurable mkt.F_ST_le

lemma oneLp_mem_H0 (mkt : MarketData Ω P) : oneLp P ∈ mkt.H0 :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_insert _ _))

lemma gainsSet_subset_H0 (mkt : MarketData Ω P) : mkt.gainsSet ⊆ mkt.H0 := fun _ hX =>
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_insert_of_mem _ hX))

lemma H0_le_L2S (mkt : MarketData Ω P) : mkt.H0 ≤ mkt.L2S := by
  refine Submodule.topologicalClosure_minimal _ ?_ mkt.isClosed_L2S
  rw [Submodule.span_le]
  rintro f (rfl | hf)
  · exact mkt.oneLp_mem_L2S
  · exact hf.1

/-- **Theorem 66, GKW projection part.** For `X ∈ L²(ℱ^S_T, ℚ)` there are `G` and `ε` with
`X = E[X]·1 + G + ε`, where `G ∈ H0`, `E[G] = 0`, `ε ∈ L²(ℱ^S_T)`, `ε ⊥ H0` (so `ε` is orthogonal
to every stochastic integral against `S`), and the Pythagorean variance identity holds.
The decomposition is unique. -/
theorem gkw_decomposition (mkt : MarketData Ω P) (X : Lp ℝ 2 P) (hX : X ∈ mkt.L2S) :
    ∃ G ε : Lp ℝ 2 P,
      G ∈ mkt.H0 ∧ ⟪G, oneLp P⟫ = 0 ∧ ε ∈ mkt.L2S ∧ ε ∈ mkt.H0ᗮ ∧
      (∀ Z ∈ mkt.gainsSet, ⟪ε, Z⟫ = 0) ∧
      X = (∫ ω, X ω ∂P) • oneLp P + G + ε ∧
      ‖X‖ ^ 2 = ‖(∫ ω, X ω ∂P) • oneLp P + G‖ ^ 2 + ‖ε‖ ^ 2 ∧
      ∀ (c : ℝ) (G' ε' : Lp ℝ 2 P), G' ∈ mkt.H0 → ⟪G', oneLp P⟫ = 0 → ε' ∈ mkt.H0ᗮ →
        X = c • oneLp P + G' + ε' → c = ∫ ω, X ω ∂P ∧ G' = G ∧ ε' = ε := by
  set c : ℝ := ∫ ω, X ω ∂P with hc
  set p : Lp ℝ 2 P := mkt.H0.starProjection X with hp
  have hp_mem : p ∈ mkt.H0 := Submodule.starProjection_apply_mem _ X
  have hε_orth : X - p ∈ mkt.H0ᗮ := Submodule.sub_starProjection_mem_orthogonal X
  have hp_one : ⟪p, oneLp P⟫ = c := by
    have h0 : ⟪X - p, oneLp P⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal mkt.oneLp_mem_H0 hε_orth
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [← h0, real_inner_comm, inner_oneLp]
  have hone_mem := mkt.oneLp_mem_H0
  refine ⟨p - c • oneLp P, X - p, ?_, ?_, ?_, hε_orth, ?_, ?_, ?_, ?_⟩
  · exact mkt.H0.sub_mem hp_mem (mkt.H0.smul_mem c hone_mem)
  · rw [inner_sub_left, inner_smul_left, hp_one, inner_oneLp_oneLp]; simp
  · exact mkt.L2S.sub_mem hX (mkt.H0_le_L2S hp_mem)
  · intro Z hZ
    exact Submodule.inner_left_of_mem_orthogonal (mkt.gainsSet_subset_H0 hZ) hε_orth
  · abel
  · have hsum : c • oneLp P + (p - c • oneLp P) = p := by abel
    rw [hsum]
    have hdecomp : X = p + (X - p) := by abel
    have h0 : ⟪p, X - p⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hp_mem hε_orth
    have hsq := norm_add_sq_real p (X - p)
    rw [← hdecomp, h0] at hsq
    linarith
  · intro c' G' ε' hG' hG'1 hε' hXeq
    have hmem : c' • oneLp P + G' ∈ mkt.H0 := mkt.H0.add_mem (mkt.H0.smul_mem c' hone_mem) hG'
    have hproj : p = c' • oneLp P + G' :=
      Submodule.eq_starProjection_of_mem_orthogonal' hmem hε' (by rw [hXeq])
    have hcc : c' = c := by
      have := hp_one
      rw [hproj, inner_add_left, inner_smul_left, inner_oneLp_oneLp, hG'1] at this
      simpa using this
    subst hcc
    refine ⟨rfl, ?_, ?_⟩
    · rw [hproj]; abel
    · rw [hproj]
      nth_rewrite 1 [hXeq]
      abel

end MarketData

end SignatureVolatility
