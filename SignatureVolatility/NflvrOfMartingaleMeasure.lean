module

public import SignatureVolatility.SatisfiesNFLVR
public import SignatureVolatility.AdmissibleGainsUnderP


@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem nflvr_of_martingale_measure {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] :
    SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) := by
  intro G f _ hf_int hf_nonneg hvanish hG_int hae
  have hint_le_zero : ∫ ω, f ω ∂ℙ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set δ := (∫ ω, f ω ∂ℙ) / 2 with hδ_def
    have hδ : 0 < δ := half_pos hpos
    have hvan : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ ω, -(δ / ((k : ℝ) + 1)) ≤ G n ω :=
      fun k => hvanish (δ / ((k : ℝ) + 1)) (div_pos hδ (by positivity))
    choose N_fn hN_fn using hvan
    let subseq : ℕ → ℕ := fun k => Nat.rec (N_fn 0) (fun j prev => max (prev + 1) (N_fn (j + 1))) k
    have hsub_mono : StrictMono subseq := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      exact Nat.lt_of_succ_le (le_max_left _ _)
    have hsub_ge : ∀ k, N_fn k ≤ subseq k := by
      intro k
      cases k with
      | zero => exact le_rfl
      | succ j => exact le_max_right _ _
    let H : ℕ → Ω → ℝ := fun k ω => G (subseq k) ω + δ
    have hH_nonneg : ∀ k ω, 0 ≤ H k ω := by
      intro k ω
      have h1 := hN_fn k (subseq k) (hsub_ge k) ω
      have h2 : δ / ((k : ℝ) + 1) ≤ δ :=
        div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
      linarith
    have hH_int : ∀ k, Integrable (H k) ℙ :=
      fun k => (hG_int (subseq k)).1.add (integrable_const δ)
    have hH_int_le : ∀ k, ∫ ω, H k ω ∂ℙ ≤ δ := by
      intro k
      rw [integral_add (hG_int (subseq k)).1 (integrable_const δ), integral_const]
      simp only [probReal_univ, one_smul]
      linarith [(hG_int (subseq k)).2]
    -- Apply `lintegral_liminf_le'` to `ENNReal.ofReal (H k ω)`
    have hmeas_H : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal (H k ω)) ℙ :=
      fun k => (hH_int k).1.aemeasurable.ennreal_ofReal
    have hfatou := lintegral_liminf_le' (u := atTop) hmeas_H
    have hae_lim : ∀ᵐ ω ∂ℙ,
        ENNReal.ofReal (f ω + δ) ≤ liminf (fun k => ENNReal.ofReal (H k ω)) atTop := by
      filter_upwards [hae] with ω hω
      have htend : Tendsto (fun k => ENNReal.ofReal (H k ω)) atTop
          (𝓝 (ENNReal.ofReal (f ω + δ))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          ((hω.comp hsub_mono.tendsto_atTop).add tendsto_const_nhds)
      exact htend.liminf_eq.ge
    have hle1 : ∫⁻ ω, ENNReal.ofReal (f ω + δ) ∂ℙ ≤
        liminf (fun k => ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ) atTop :=
      (lintegral_mono_ae hae_lim).trans hfatou
    have hle2 : ∀ k, ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ ≤ ENNReal.ofReal δ := by
      intro k
      rw [← ofReal_integral_eq_lintegral_ofReal (hH_int k) (Eventually.of_forall (hH_nonneg k))]
      exact ENNReal.ofReal_le_ofReal (hH_int_le k)
    have hliminf_le : liminf (fun k => ∫⁻ ω, ENNReal.ofReal (H k ω) ∂ℙ) atTop ≤ ENNReal.ofReal δ := by
      refine liminf_le_of_frequently_le' (Frequently.of_forall hle2)
    have hfδ_int : Integrable (fun ω => f ω + δ) ℙ := hf_int.add (integrable_const δ)
    have hfδ_nonneg : 0 ≤ᵐ[ℙ] fun ω => f ω + δ :=
      Eventually.of_forall fun ω => add_nonneg (hf_nonneg ω) hδ.le
    have hlhs : ∫⁻ ω, ENNReal.ofReal (f ω + δ) ∂ℙ = ENNReal.ofReal (∫ ω, (f ω + δ) ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hfδ_int hfδ_nonneg).symm
    have hcomb : ENNReal.ofReal (∫ ω, (f ω + δ) ∂ℙ) ≤ ENNReal.ofReal δ := by
      rw [← hlhs]
      exact hle1.trans hliminf_le
    have hreal_le : ∫ ω, (f ω + δ) ∂ℙ ≤ δ :=
      (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hcomb
    rw [integral_add hf_int (integrable_const δ), integral_const, probReal_univ, one_smul] at hreal_le
    linarith
  have hf_eq : f =ᵐ[ℙ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf_nonneg) hf_int).mp
      (le_antisymm hint_le_zero (integral_nonneg hf_nonneg))
  exact hf_eq

end SignatureVolatility
