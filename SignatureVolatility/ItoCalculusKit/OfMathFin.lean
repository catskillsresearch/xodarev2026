module

public import SignatureVolatility.MemTwDualOfMemL2w
public import SignatureVolatility.ProlongedBrownianSetup.SignatureOfBM
public import SignatureVolatility.TheoremA


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# An `ItoCalculusKit` over the Brownian setup, and `theorem_A` there

**Read this before citing anything from this file.** The kit built here is the *degenerate*
inhabitant of `ItoCalculusKit`:

* `itoInt H t ω = 0`, `quadVar H t ω = 0`, `doleansExp σ t ω = 1`.

It satisfies every field of the structure as currently axiomatised, because no field forces
`itoInt` to be a stochastic integral against the driver `W`. It is **not** an Itô integral, and
it does not use MathFin; the name `itoCalculusKit_of_mathfin` is kept only because the campaign
plan refers to it. Consequently `theorem_A_of_brownian` is a type-correct instance of
`theorem_A` whose solution is the constant process `S ≡ s₀` and whose "SDE" reads
`S̃ t = s₀` almost surely: it carries no information about a Brownian SDE.

The one field with real content is the pathwise square-integrability of
`σ_s = ⟨ℓ, Ŵ_s⟩` on `[0, T]` in `novikov_doob_l2_martingale`. It is proved from almost sure
path continuity of the driver, not from `HypH3` (see
`ae_integrableOn_sq_dualPairing_of_brownian`).

## Why the kit is built over the Brownian setup only

`ItoCalculusKit` cannot be inhabited over an arbitrary `ProlongedBrownianSetup`. The structure
puts no regularity in time on `W` or `sig2`, so `s ↦ σ_s(ω)` may fail to be measurable; then
`∫₀ᵀ σ_s² ds` is `0` by convention, `HypH3` holds trivially, and the last conclusion of
`novikov_doob_l2_martingale` is false. Path continuity of a `MultiBrownian` rules this out.

A nontrivial kit (Itô integral, Doléans-Dade exponential, Novikov) wired to MathFin is future
work; it needs a joint Brownian motion and a Novikov criterion that are not yet available here.
-/

namespace ExtTensorAlgebra

/-- Coefficients of `exp⊗(v x)` are continuous in `x` when the coordinates of `v` are. -/
lemma continuous_tensorExp_coeff {X : Type*} [TopologicalSpace X] {d : ℕ}
    {v : X → Fin d → ℝ} (hv : ∀ j, Continuous (fun x => v x j)) (I : Word d) :
    Continuous (fun x => (tensorExp (v x)).coeff I) := by
  have hprod : Continuous (fun x => (I.map (v x)).prod) := by
    induction I with
    | nil => simpa using continuous_const
    | cons i I ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (hv i).mul ih
  exact hprod.div_const _

/-- Level pairings against `exp⊗(v x)` are continuous in `x`. -/
lemma continuous_levelInner_tensorExp {X : Type*} [TopologicalSpace X] {d : ℕ}
    {v : X → Fin d → ℝ} (hv : ∀ j, Continuous (fun x => v x j)) (ℓ : ExtTensorAlgebra d)
    (n : ℕ) : Continuous (fun x => levelInner ℓ (tensorExp (v x)) n) :=
  continuous_finsetSum _ fun I _ => continuous_const.mul (continuous_tensorExp_coeff hv I)

end ExtTensorAlgebra

open ExtTensorAlgebra

/-- Along a continuous path `v`, the pairing `x ↦ ⟨ℓ, exp⊗(v x)⟩` with `ℓ ∈ ℓ²_w` is continuous
on compact sets (Weierstrass M-test, using the subfactorial growth of `w`). -/
lemma continuousOn_dualPairing_tensorExp {X : Type*} [TopologicalSpace X] {d : ℕ} {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra d} (hℓ : MemL2w w ℓ) {v : X → Fin d → ℝ}
    (hv : ∀ j, Continuous (fun x => v x j)) {K : Set X} (hK : IsCompact K) :
    ContinuousOn (fun x => dualPairing ℓ (tensorExp (v x))) K := by
  have hr : Continuous (fun x => Real.sqrt (∑ i, v x i ^ 2)) :=
    (continuous_finsetSum _ fun i _ => (hv i).pow 2).sqrt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hr.continuousOn
  set R : ℝ := max C 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hDual : MemTwDual w ℓ := (memTwDual_of_memL2w w hℓ).1
  refine continuousOn_tsum (u := fun n => normWDual w ℓ * (w n * (R ^ n / (n.factorial : ℝ))))
    (fun n => (continuous_levelInner_tensorExp hv ℓ n).continuousOn)
    ((hw.subfactorial_nonneg hR0).mul_left _) fun n x hx => ?_
  have hrx : Real.sqrt (∑ i, v x i ^ 2) ≤ R := by
    have := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hℓn : ℓ.levelNorm n ≤ normWDual w ℓ * w n :=
    (div_le_iff₀ (w.pos n)).mp (normWDual.levelNorm_div_le w hDual n)
  calc ‖levelInner ℓ (tensorExp (v x)) n‖
      ≤ ℓ.levelNorm n * (tensorExp (v x)).levelNorm n := levelInner.abs_le ℓ _ n
    _ = ℓ.levelNorm n * (Real.sqrt (∑ i, v x i ^ 2) ^ n / (n.factorial : ℝ)) := by
        rw [tensorExp_levelNorm]
    _ ≤ (normWDual w ℓ * w n) * (R ^ n / (n.factorial : ℝ)) :=
        mul_le_mul hℓn
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hrx n)
            (Nat.cast_nonneg _))
          (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) n) (Nat.cast_nonneg _))
          (mul_nonneg (normWDual.nonneg w hDual) (w.pos n).le)
    _ = normWDual w ℓ * (w n * (R ^ n / (n.factorial : ℝ))) := mul_assoc _ _ _

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Almost every path of the time-augmented driver `(t, W_t)` is continuous in real time. -/
lemma MultiBrownian.ae_continuous_wAug (B : MultiBrownian Ω P d) :
    ∀ᵐ ω ∂P, ∀ j : Fin (d + 1), Continuous (fun t => MultiBrownian.wAug B t ω j) := by
  have h : ∀ᵐ ω ∂P, ∀ i : Fin d, Continuous (fun t => B.Wnn t ω i) :=
    ae_all_iff.mpr fun i => (B.isBrownian i).cont
  filter_upwards [h] with ω hω j
  by_cases hj : (j : ℕ) = 0
  · simp only [MultiBrownian.wAug, hj, ↓reduceDIte]
    exact continuous_id
  · simp only [MultiBrownian.wAug, hj, ↓reduceDIte]
    exact (hω _).comp continuous_real_toNNReal

/-- **Pathwise square-integrability of the signature volatility** over a Brownian driver: for
`ℓ ∈ ℓ²_w` and `w` satisfying H2, almost every path `s ↦ ⟨ℓ, Ŵ_s⟩` is continuous on `[0, T]`,
so its square is integrable there. No use of `HypH3`. -/
lemma ae_integrableOn_sq_dualPairing_of_brownian {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun s => (dualPairing ℓ ((prolongedBrownianSetup_of_brownian B hT).W_hat s ω)) ^ 2)
      (Icc 0 T) volume := by
  filter_upwards [B.ae_continuous_wAug] with ω hω
  have hc : ContinuousOn (fun s => dualPairing ℓ (runningSig B s ω)) (Icc 0 T) :=
    continuousOn_dualPairing_tensorExp hw hℓ.mem_l2w
      (fun j => (hω j).sub continuous_const) isCompact_Icc
  have heq : ∀ s, (prolongedBrownianSetup_of_brownian B hT).W_hat s ω = runningSig B s ω :=
    fun s => sig2OfBrownian_zero_left B s ω
  simp only [heq]
  exact (hc.pow 2).integrableOn_Icc

/-- **Degenerate `ItoCalculusKit` over the Brownian setup** (`itoInt = 0`, `quadVar = 0`,
`doleansExp = 1`). See the module docstring: this is *not* an Itô integral and does not use
MathFin; the name is the campaign plan's. A genuine MathFin wiring is future work. -/
def itoCalculusKit_of_mathfin {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ItoCalculusKit Ω P d T (prolongedBrownianSetup_of_brownian B hT) where
  itoInt := fun _ _ _ => 0
  itoInt_zero := fun _ _ => rfl
  itoInt_meas := fun _ _ => measurable_const
  itoInt_adapted := fun _ _ _ => measurable_const
  quadVar := fun _ _ _ => 0
  quadVar_zero := fun _ _ => rfl
  quadVar_meas := fun _ _ => measurable_const
  quadVar_adapted := fun _ _ _ => measurable_const
  doleansExp := fun _ _ _ => 1
  doleansExp_def := fun _ _ _ => by simp
  doleans_sde := fun _ _ _ _ _ => ae_of_all _ fun _ => by simp
  stopped_l2_localisation := by
    intro w ℓ s₀ S₁ S₂ σ h₁ h₂
    refine ⟨fun _ _ => 0, fun _ => continuousOn_const, fun _ _ _ => le_rfl,
      fun _ _ _ => by simp, fun _ t ht => ?_⟩
    filter_upwards [h₁ t ht, h₂ t ht] with ω e₁ e₂
    rw [e₁, e₂]
  novikov_doob_l2_martingale := by
    intro w hw ℓ hℓ s₀ _ σ S _
    refine ⟨fun s t _ _ _ => ⟨integrable_const _, ?_⟩,
      ⟨fun _ => |s₀|, measurable_const, fun ω t _ => by simp [S], integrable_const _⟩,
      ae_integrableOn_sq_dualPairing_of_brownian B hT hw hℓ⟩
    change P[fun _ : Ω => s₀ * (1 : ℝ) | _] =ᵐ[P] fun _ => s₀ * 1
    rw [condExp_const
      ((prolongedBrownianSetup_of_brownian B hT).signatureFiltration.le_ambient s)]

/-- `theorem_A` instantiated at the Brownian setup and the degenerate kit above.

**Scope.** Because `itoCalculusKit_of_mathfin` has `itoInt = 0`, the solution produced is the
constant `S ≡ s₀` and the uniqueness hypothesis reads `S̃ t = s₀` a.s. for each `t`. This checks
that `theorem_A`'s hypotheses are jointly satisfiable over a Brownian driver; it is not Theorem A
of the paper for a Brownian SDE. -/
theorem theorem_A_of_brownian (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T
      (SignatureVolatilityModel.sigma M (prolongedBrownianSetup_of_brownian B M.hT))) :
    ∃ sol : SignaturePriceSolution M (prolongedBrownianSetup_of_brownian B M.hT)
        (itoCalculusKit_of_mathfin B M.hT),
      ∀ S_tilde : ℝ → Ω → ℝ,
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P,
          S_tilde t ω = M.s₀ + (itoCalculusKit_of_mathfin B M.hT).itoInt
            (fun s ω' => S_tilde s ω' *
              SignatureVolatilityModel.sigma M (prolongedBrownianSetup_of_brownian B M.hT) s ω')
            t ω) →
        ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P, S_tilde t ω = sol.S t ω :=
  theorem_A M (prolongedBrownianSetup_of_brownian B M.hT) (itoCalculusKit_of_mathfin B M.hT) h3

end SignatureVolatility
