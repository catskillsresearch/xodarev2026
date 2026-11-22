module

public import SignatureVolatility.ItoCalculusKit.DoobEnvelope
public import SignatureVolatility.ItoCalculusKit.NovikovMartingale
public import SignatureVolatility.ItoCalculusKit.SubseqUniform

@[expose] public section

open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

/-!
# A square-integrable envelope for the Doléans exponential of the signature volatility

At a time `t` where the kit Riemann sums converge, their limit is identified (along the
subsequence `N_j`, simultaneously for all `t`, `SubseqUniform`) with the continuous version `Ĩ_t`;
where they do not converge, `limUnder` returns the fixed junk value `junkReal`.  Hence
`Z_t ≤ max(exp(Ĩ_t - ½∫σ²), e^{junkReal})` for **every** `t ∈ [0, T]` almost surely, and Doob's
`L²` inequality on the dyadic martingale `Z` (`DoobEnvelope`) bounds the first term.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The value `limUnder` returns on a non-convergent real sequence. -/
def junkReal : ℝ := Classical.choice (⟨0⟩ : Nonempty ℝ)

lemma limUnder_eq_junkReal {u : ℕ → ℝ} (h : ¬ ∃ x, Tendsto u atTop (𝓝 x)) :
    limUnder atTop u = junkReal := by
  have h' : ¬ ∃ x, map u atTop ≤ 𝓝 x := h
  simp only [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, h',
    dite_false]
  rfl

section Envelope

variable {T : ℝ} (B : MultiBrownian Ω P d)

lemma kitItoIntRaw_eq_limUnder (hd : 0 < d) {H : ℝ → Ω → ℝ} {K : ℝ}
    (hH : HolderAdapted8 B H T K) {t : ℝ} (ht : t ∈ Icc 0 T) (ω : Ω) :
    kitItoIntRaw B H t ω =
      limUnder atTop fun n : ℕ => unifRiemann B (kitDriver hd) H t (n + 1) ω := by
  simp only [kitItoIntRaw, hd, ↓reduceDIte, itoIntegral_process, ht.1]
  congr 1
  funext n
  rw [itoRiemann_process_eq_unifRiemann]
  unfold unifRiemann
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h0, h1⟩ := unifGrid_mem ht.1 n.succ_pos (Finset.mem_range.mp hi).le
  rw [forceMeasurableProcess_eq_of_adapted B (hH.meas _ h0 (h1.trans ht.2))]

lemma tendsto_subseqN_sub_one : Tendsto (fun j => subseqN j - 1) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun j hj => ?_⟩
  have h1 : j < 2 ^ j := Nat.lt_two_pow_self
  have h2 : 2 ^ j ≤ subseqN j := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Envelope of the Doléans exponential** of `σ = ⟨ℓ, Ŵ⟩` under H1–H3. -/
theorem exists_envelope_kitDoleansExp_signatureSigma (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) :
    ∃ G : Ω → ℝ, Measurable G ∧ MemLp G 2 P ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, kitDoleansExp B (signatureSigma B hT ℓ) t ω ≤ G ω := by
  set σ := signatureSigma B hT ℓ with hσ
  set Z := kitDoleansExp B σ with hZ
  obtain ⟨K, hK⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  obtain ⟨Y, hYc, hY⟩ := exists_continuous_version_kitItoIntRaw B hd hK hT.le
  have hsub := ae_tendsto_subseq_of_continuous_version B hd hT hK
    (ae_holder_signatureSigma B hT hw hℓ) hYc hY
  set Xt : ℝ → Ω → ℝ := fun t ω =>
    Real.exp (Y (Real.toNNReal t) ω - (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (σ s ω) ^ 2) with hXt
  have hX : ∀ n j, Z (dyadicGrid T n j) =ᵐ[P]
      P[Z T | (pathFiltration B).σAlg (dyadicGrid T n j)] := by
    intro n j
    have hq := dyadicGrid_mem hT.le n j
    have h := (condExp_kitDoleansExp_signatureSigma B hd hT hw hℓ h3 1 hq.1 hq.2 le_rfl).2
    simp only [one_mul] at h
    exact h.symm
  have hL2 : MemLp (Z T) 2 P := by
    have := memLp_kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 ⟨hT.le, le_rfl⟩ 2
      (by norm_num)
    exact_mod_cast this
  have hgrid : ∀ᵐ ω ∂P, ∀ n j, Y (Real.toNNReal (dyadicGrid T n j)) ω =
      kitItoIntRaw B σ (dyadicGrid T n j) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro j
    have hq := dyadicGrid_mem hT.le n j
    filter_upwards [hY (Real.toNNReal (dyadicGrid T n j))
      (by rw [Real.coe_toNNReal _ hq.1]; exact hq.2)] with ω hω
    rw [hω, Real.coe_toNNReal _ hq.1]
  have hXtc : ∀ ω, ContinuousOn (fun t => Xt t ω) (Icc 0 T) := by
    intro ω
    have hσc := continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω
    have hint : IntervalIntegrable (fun s => (σ s ω) ^ 2) volume 0 T :=
      (hσc.pow 2).intervalIntegrable_of_Icc hT.le
    have hprim := intervalIntegral.continuousOn_primitive_interval' hint
      (Set.left_mem_uIcc (a := (0 : ℝ)) (b := T))
    rw [Set.uIcc_of_le hT.le] at hprim
    exact Real.continuous_exp.comp_continuousOn
      ((((hYc ω).comp continuous_real_toNNReal).continuousOn).sub
        (continuousOn_const.mul hprim))
  have hXtae : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xt t ω) (Icc 0 T) ∧
      ∀ n j, Z (dyadicGrid T n j) ω = Xt (dyadicGrid T n j) ω := by
    filter_upwards [hgrid] with ω hω
    refine ⟨hXtc ω, fun n j => ?_⟩
    have hq := dyadicGrid_mem hT.le n j
    rw [hZ, kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hq ω, ← hω n j]
  obtain ⟨E, hEm, hE0, hEL, hEdom⟩ := exists_envelope_of_dyadic_martingale B hT
    (fun t => measurable_kitDoleansExp B σ t) hX hL2 hXtae
  refine ⟨fun ω => E ω + Real.exp junkReal, hEm.add_const _, hEL.add (memLp_const _), ?_⟩
  filter_upwards [hEdom, hsub] with ω hdom hs
  intro t ht
  have hQ : 0 ≤ ∫ s in (0 : ℝ)..t, (σ s ω) ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _
  have hexp0 : 0 < Real.exp junkReal := Real.exp_pos _
  rw [hZ, kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 ht ω,
    kitItoIntRaw_eq_limUnder B hd hK ht ω]
  by_cases hc : ∃ x, Tendsto (fun n : ℕ => unifRiemann B (kitDriver hd) σ t (n + 1) ω) atTop (𝓝 x)
  · obtain ⟨x, hx⟩ := hc
    rw [hx.limUnder_eq]
    have hsubx : Tendsto (fun j => unifRiemann B (kitDriver hd) σ t (subseqN j) ω) atTop
        (𝓝 x) := by
      refine (hx.comp tendsto_subseqN_sub_one).congr fun j => ?_
      simp only [Function.comp_apply, Nat.sub_add_cancel (subseqN_pos j)]
    have hxY : x = Y (Real.toNNReal t) ω := tendsto_nhds_unique hsubx (hs t ht)
    rw [hxY]
    have := (le_abs_self (Xt t ω)).trans (hdom t ht)
    exact this.trans (by linarith)
  · rw [limUnder_eq_junkReal hc]
    have : Real.exp (junkReal - (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (σ s ω) ^ 2) ≤
        Real.exp junkReal := Real.exp_le_exp.mpr (by linarith)
    linarith [hE0 ω]

end Envelope

end SignatureVolatility
