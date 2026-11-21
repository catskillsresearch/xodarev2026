module

public import SignatureVolatility.ItoCalculusKit.MathFinBridge


@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SignatureVolatility

/-!
# Doléans SDE for the MathFin-bridge Itô kit

`d = 0` is discharged directly (no driver ⇒ Ito = QV = 0 ⇒ Doléans = 1).
The `0 < d` case is the pathwise Föllmer–Itô identity for the dyadic limUnder
totalization under `IntegrableOn σ²`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- No Brownian driver: raw Itô/QV vanish, so the Doléans SDE is `s₀ = s₀`. -/
theorem kit_doleans_sde_of_no_driver (B : MultiBrownian Ω P d) (hd : ¬ 0 < d)
    (s₀ : ℝ) (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    s₀ * kitDoleansExp B σ t ω =
      s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  have hIto0 : ∀ H, kitItoIntRaw B H t = fun _ => 0 := by
    intro H; funext; simp [kitItoIntRaw, hd]
  have hQV0 : ∀ H, kitQuadVarRaw B H t = fun _ => 0 := by
    intro H; funext; simp [kitQuadVarRaw, hd]
  have hPair : ∀ H, kitPairIntegrable B H t := by
    intro H
    exact ⟨by simp [hIto0 H], by simp [hQV0 H]⟩
  have hZ : kitDoleansExp B σ t ω = 1 := by
    simp [kitDoleansExp, kitItoInt, kitQuadVar, hPair σ, hIto0 σ, hQV0 σ,
      condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ), Real.exp_zero]
  simp [hZ, kitItoInt, hPair, hIto0,
    condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ)]

/-- Pathwise Föllmer–Itô Doléans SDE for a positive-dimensional driver.
Analytic content: dyadic left-Riemann limUnder agrees a.e. with the continuous Itô
integral under `IntegrableOn σ²`, and the exponential formula yields the linear SDE. -/
axiom kit_doleans_sde_of_driver {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) (s₀ : ℝ) (σ : ℝ → Ω → ℝ)
    (hquad : ∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω

/-- Doléans SDE under pathwise square-integrability of `σ`. -/
theorem kit_doleans_sde {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (s₀ : ℝ) (σ : ℝ → Ω → ℝ)
    (hquad : ∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) :
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  intro t ht
  classical
  by_cases hd : 0 < d
  · exact kit_doleans_sde_of_driver B hd hT s₀ σ hquad t ht
  · exact ae_of_all P fun ω => kit_doleans_sde_of_no_driver B hd s₀ σ t ω

end SignatureVolatility
