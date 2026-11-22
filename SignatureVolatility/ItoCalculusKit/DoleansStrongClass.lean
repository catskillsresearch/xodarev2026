module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ItoCalculusKit.NovikovDoob
public import SignatureVolatility.ItoCalculusKit.ItoQuadDoleans

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# The Doléans price is a kit strong solution

Under H1–H3 the Doléans price `S = s₀ · Z` lies in `KitStrongSolutionClass`: its supremum on
`[0, T]` has a square-integrable envelope (`kit_novikov_doob_l2_martingale`) and the integrand
`S σ` is `L⁴`-Hölder-`1/2` adapted (`holderAdapted_kitDoleansExp_mul`; for `d = 0`, `Z ≡ 1` and
`holderAdapted_signatureSigma`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **The constructed Doléans solution is in the strong-solution class.** -/
theorem kit_doleans_strong_class {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) (s₀ : ℝ)
    (hs₀ : 0 < s₀) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    KitStrongSolutionClass P T σ (fun t ω => s₀ * paperDoleansExp B hT σ t ω) := by
  intro setup σ h3
  obtain ⟨-, hsup, -⟩ := kit_novikov_doob_l2_martingale B hT w hw ℓ hℓ s₀ hs₀ h3
  have hreg : ∃ K, HolderAdapted B (fun s ω => s₀ * kitDoleansExp B σ s ω * σ s ω) T K := by
    by_cases hd : 0 < d
    · obtain ⟨K, hK⟩ := holderAdapted_kitDoleansExp_mul B hd hT hw hℓ h3
      have e : (fun s ω => s₀ * kitDoleansExp B σ s ω * σ s ω) =
          fun s ω => s₀ * (kitDoleansExp B σ s ω * σ s ω) := by
        funext s ω; ring
      rw [e]
      exact ⟨_, hK.const_mul s₀⟩
    · obtain ⟨K, hK⟩ := holderAdapted_signatureSigma B hT hw hℓ T
      have e : (fun s ω => s₀ * kitDoleansExp B σ s ω * σ s ω) = fun s ω => s₀ * σ s ω := by
        funext s ω; rw [kitDoleansExp_of_no_driver B hd, mul_one]
      rw [e]
      exact ⟨_, hK.const_mul s₀⟩
  obtain ⟨K, hK⟩ := hreg
  exact ⟨hsup, K, hK.K_nonneg, fun u hu => hK.memLp u hu.1 hu.2,
    fun u v h0 huv hv => hK.holder u v h0 huv hv⟩

end SignatureVolatility
