/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib

/-!
# Palomar Challenge (statement of record)

Mathlib-only statement file for Xodarev’s Theorems A–D on signature volatility
models. Compared declarations match `SignatureVolatilityComparator/Solution.lean`
via the `SignatureVolatility/` library. Framing: reconstruction/verification of
Akmal Xodarev, *On the Structural Foundations of Signature Volatility Models*
(arXiv:2605.17142). Akmal Xodarev did not participate in or endorse this
formalization. Every compared theorem's Solution proof uses only `propext` /
`Quot.sound` / `Classical.choice`.
-/
@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace SignatureVolatility

universe u_1

noncomputable section

structure Weight where
  toFun : ℕ → ℝ
  w_zero : toFun 0 = 1
  pos : ∀ n : ℕ, 0 < toFun n
  mono : Monotone toFun

instance : CoeFun Weight (fun _ => ℕ → ℝ) := ⟨Weight.toFun⟩

abbrev Letter (d : ℕ) := Fin d

abbrev Word (d : ℕ) := List (Letter d)

@[ext]
structure ExtTensorAlgebra (d : ℕ) where
  coeff : Word d → ℝ

namespace ExtTensorAlgebra

instance {d : ℕ} : Zero (ExtTensorAlgebra d) := ⟨⟨fun _ => 0⟩⟩
instance {d : ℕ} : Add (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I + b.coeff I⟩⟩
instance {d : ℕ} : Neg (ExtTensorAlgebra d) := ⟨fun a => ⟨fun I => -a.coeff I⟩⟩
instance {d : ℕ} : Sub (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I - b.coeff I⟩⟩
instance {d : ℕ} : SMul ℝ (ExtTensorAlgebra d) := ⟨fun c a => ⟨fun I => c * a.coeff I⟩⟩

instance {d : ℕ} : AddCommGroup (ExtTensorAlgebra d) where
  add_assoc a b c := by ext I; exact add_assoc _ _ _
  zero_add a := by ext I; exact zero_add _
  add_zero a := by ext I; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext I; exact neg_add_cancel _
  add_comm a b := by ext I; exact add_comm _ _

instance {d : ℕ} : Module ℝ (ExtTensorAlgebra d) where
  one_smul a := by ext I; exact one_mul _
  mul_smul r s a := by ext I; exact mul_assoc _ _ _
  smul_zero r := by ext I; exact mul_zero _
  smul_add r a b := by ext I; exact mul_add _ _ _
  add_smul r s a := by ext I; exact add_mul _ _ _
  zero_smul a := by ext I; exact zero_mul _

end ExtTensorAlgebra

namespace ExtTensorAlgebra

def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop := sorry

abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ := sorry

def levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ := sorry

def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ := sorry

def concat {d : ℕ} (a b : ExtTensorAlgebra d) : ExtTensorAlgebra d := sorry

def evalShuffleBasis {d : ℕ} (I J : Word d) (X : ExtTensorAlgebra d) : ℝ := sorry

def shuffleWords {d : ℕ} : Word d → Word d → List (Word d) := sorry

def basisWord {d : ℕ} (I : Word d) : ExtTensorAlgebra d := sorry

infixl:70 " ⊗ₜ " => concat

end ExtTensorAlgebra

structure IndexedFiltration (Ω : Type u_1) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀

def wordsOfLength (d : ℕ) : ℕ → Finset (Word d) := sorry

def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop := sorry

def MemL2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop := sorry

def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop := sorry

def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ := sorry

def norm2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ := sorry

def norm2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ := sorry

def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ := sorry

def generatedFiltration {Ω : Type u_1} {ι : Type*} [m₀ : MeasurableSpace Ω]
    (Z : ℝ → ι → Ω → ℝ) (hmeas : ∀ t i, Measurable (Z t i)) : IndexedFiltration Ω := sorry

def SatisfiesNFLVR {Ω : Type u_1} [MeasurableSpace Ω] (ℙ : Measure Ω)
    (AdmissibleTerminalGains : Set (Ω → ℝ)) : Prop := sorry

def AdmissibleGainsUnderP {Ω : Type u_1} [MeasurableSpace Ω] (ℙ : Measure Ω) : Set (Ω → ℝ) := sorry

def projLe {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d := sorry

def replicableStarProjection {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    (K : Submodule ℝ H_S) [hK : K.HasOrthogonalProjection] (X : H_S) : H_S := sorry

structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ

structure HypH2 (w : Weight) where
  C_w : ℝ
  one_le_Cw : 1 ≤ C_w
  submult : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n
  subfactorial : ∀ R : ℝ, 0 < R → Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ)))

structure HypH3 {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

structure SignatureVolatilityModel where
  d : ℕ
  hd : 0 < d
  T : ℝ
  hT : 0 < T
  w : Weight
  ℓ : ExtTensorAlgebra (d + 1)
  s₀ : ℝ
  hs₀ : 0 < s₀
  h1 : HypH1 w ℓ
  h2 : HypH2 w
  h3 : HypH3 hd ℓ

structure ProlongedBrownianSetup (Ω : Type u_1) [m₀ : MeasurableSpace Ω]
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
  /-- Appendix A Brownian signature factorial level-decay estimate: for each `p ≥ 1`, there exist
  constants `C_p ≥ 0` and `R_p ≥ 0` controlling the `L^p`-norm of level-`n` signature norms by
  `C_p * R_p^n / n!`, together with uniform `L^p` control of weighted sums. -/
  factorial_moment_control : ∀ (p : ℝ), 1 ≤ p → ∃ (C_p R_p : ℝ), 0 ≤ C_p ∧ 0 ≤ R_p ∧
    ∀ (w_fn : ℕ → ℝ), (∀ n, 0 ≤ w_fn n) →
      Summable (fun n : ℕ => w_fn n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) →
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
        (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2 0 t ω).levelNorm n)) ∧
        Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p) ℙ ∧
        (∫ ω, (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p ∂ℙ) ≤
          (∑' n : ℕ, w_fn n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) ^ p

namespace ProlongedBrownianSetup

def W_hat {Ω : Type u_1} [m₀ : MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) :
    ExtTensorAlgebra (d + 1) := sorry

def signatureFiltration {Ω : Type u_1} [m₀ : MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω := sorry

end ProlongedBrownianSetup

structure ItoCalculusKit (Ω : Type u_1) [m₀ : MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (d : ℕ) (T : ℝ)
    (setup : ProlongedBrownianSetup Ω ℙ d T) where
  itoInt : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  itoInt_zero : ∀ H ω, itoInt H 0 ω = 0
  itoInt_meas : ∀ H t, Measurable (itoInt H t)
  itoInt_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (itoInt H s.1)
  quadVar : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  quadVar_zero : ∀ H ω, quadVar H 0 ω = 0
  quadVar_meas : ∀ H t, Measurable (quadVar H t)
  quadVar_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (quadVar H s.1)
  doleansExp : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  doleansExp_def : ∀ σ t ω,
    doleansExp σ t ω = Real.exp (itoInt σ t ω - (1 / 2 : ℝ) * quadVar σ t ω)
  doleans_sde : ∀ (s₀ : ℝ) (σ : ℝ → Ω → ℝ),
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ,
      s₀ * doleansExp σ t ω = s₀ + itoInt (fun s ω' => (s₀ * doleansExp σ s ω') * σ s ω') t ω
  stopped_l2_localisation : ∀ (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) (s₀ : ℝ)
    (S₁ S₂ : ℝ → Ω → ℝ),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = s₀ + itoInt (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₂ t ω = s₀ + itoInt (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) → ∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 T, S₁ t ω = S₂ t ω))
  novikov_doob_l2_martingale : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * doleansExp σ t ω
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) ℙ ∧
      ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ ω, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)

namespace SignatureVolatilityModel

def sigma {Ω : Type u_1} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (t : ℝ) (ω : Ω) : ℝ := sorry

end SignatureVolatilityModel

structure SignaturePriceSolution {Ω : Type u_1} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) where
  S : ℝ → Ω → ℝ
  S_zero : ∀ ω, S 0 ω = M.s₀
  S_meas : ∀ t, Measurable (S t)
  S_adapted : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (S s.1)
  S_strictly_pos : ∀ t ω, 0 < S t ω
  doleans_repr : ∀ t ω,
    S t ω = M.s₀ * Real.exp (ito.itoInt (SignatureVolatilityModel.sigma M setup) t ω -
      (1 / 2 : ℝ) * ito.quadVar (SignatureVolatilityModel.sigma M setup) t ω)
  solves_sde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
    S t ω = M.s₀ + ito.itoInt (fun s ω' => S s ω' * SignatureVolatilityModel.sigma M setup s ω') t ω
  sup_l2_integrable : ∃ S_sup : Ω → ℝ, Measurable S_sup ∧
    (∀ ω, ∀ t ∈ Icc 0 M.T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ
  is_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
    Integrable (S t) ℙ ∧
    ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s

structure IsSpecialSemimartingale {Ω : Type u_1} [MeasurableSpace Ω]
    (ℙ : Measure Ω) (ℱ : IndexedFiltration Ω) (T : ℝ) (X : ℝ → Ω → ℝ) where
  M_part : ℝ → Ω → ℝ
  A_part : ℝ → Ω → ℝ
  decomp : ∀ t ∈ Icc 0 T, ∀ ω, X t ω = X 0 ω + M_part t ω + A_part t ω
  M_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    Integrable (M_part t) ℙ ∧ ℙ[M_part t | ℱ.σAlg s] =ᵐ[ℙ] M_part s
  M_l2_bdd : Integrable (fun ω => (M_part T ω) ^ 2) ℙ
  A_integrable_var : ∃ V : Ω → ℝ, Integrable V ℙ ∧ ∀ t ∈ Icc 0 T, ∀ ω, |A_part t ω| ≤ V ω

structure ClassicalRiccatiSolution {d : ℕ} (w : Weight) (T : ℝ)
    (R_op : ExtTensorAlgebra (d + 1) → ExtTensorAlgebra (d + 1))
    (u₀ : ExtTensorAlgebra (d + 1)) where
  ψ : ℝ → ExtTensorAlgebra (d + 1)
  mem_Tw : ∀ t ∈ Icc 0 T, MemTw w (ψ t)
  uniform_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, normW w (ψ t) ≤ M
  init : ψ 0 = u₀
  integral_eq : ∀ t ∈ Icc 0 T, ∀ I : Word (d + 1),
    ContinuousOn (fun s => (R_op (ψ s)).coeff I) (Icc 0 T) ∧
      (ψ t).coeff I = u₀.coeff I + ∫ s in (0 : ℝ)..t, (R_op (ψ s)).coeff I

structure SignatureRiccatiKit (Ω : Type u_1) [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T) where
  /-- Every finite coordinate `t ↦ ⟨e_I, Ŵ_t⟩` is a special semimartingale on `[0, T]`. -/
  coord_special_semimartingale : ∀ I : Word (M.d + 1),
    IsSpecialSemimartingale ℙ setup.signatureFiltration M.T (fun t ω => (setup.W_hat t ω).coeff I)
  /-- Riccati vector field `ℛ` on `T_w` extending `riccatiOpBounded` from `𝒟_fin`. -/
  R_op : ExtTensorAlgebra (M.d + 1) → ExtTensorAlgebra (M.d + 1)
  /-- Equivalence between global classical Riccati solvability on `[0, T]` and bounded
  exponential-affine conditional signature transforms `E[exp(⟨u₀, Ŵ_T⟩) | ℱ^{\widehat{W}}_t] =
  exp(⟨ψ(T - t), Ŵ_t⟩)` for `u₀ ∈ 𝒟_fin` (Theorem 4.2(4)). -/
  affine_riccati_duality : ∀ (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)),
    (∃ sol : ClassicalRiccatiSolution M.w M.T R_op u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
        ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
          setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (setup.W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T R_op u₀.1)

structure PriceFiltrationSignatureSpace (H_S : Type u_1) [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] (d : ℕ) where
  /-- Constant payoff `1 ∈ L^2(ℱ^S_T, ℚ)`. -/
  oneVec : H_S
  /-- Dynamic self-financing stochastic integral subspace `{∫_0^T H_s dS_s} ⊆ L^2(ℱ^S_T, ℚ)`. -/
  dynamicGainSubspace : Submodule ℝ H_S
  /-- Projected signature coordinate `Y_I = E_ℚ[⟨e_I, Ŵ_T⟩ | ℱ^S_T] ∈ H_S`. -/
  Y : Word (d + 1) → H_S
  /-- European call payoffs `(S_T - K)^+` indexed by strike `K ∈ (0, ∞)`. -/
  callPayoff : ℝ → H_S
  /-- Davis–Obłój / monotone class / Stone–Weierstrass spanning bridge (Appendix C):
  for any strike set `𝒦 ⊆ (0, ∞)` dense in `(0, ∞)` and any finite set of projected signature
  coordinates `𝒜_N = {Y_I : 1 ≤ |I| ≤ N}`, dynamic trading in `S` plus static positions in calls
  `{(S_T - K)^+ : K ∈ 𝒦}` and `𝒜_N` spans a dense subspace of `H_S` iff the finite-level
  subspace `𝒱^{(N)}_S` is dense in the full signature span `𝒱^{(∞)}_S = H_S`. -/
  davis_obloj_bridge : ∀ (𝒦 : Set ℝ), (Ioi (0 : ℝ) ⊆ closure 𝒦) →
    (Submodule.topologicalClosure
      (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S) = ⊤) ∧
    (∀ N : ℕ,
      Submodule.topologicalClosure
        (dynamicGainSubspace ⊔
          Submodule.span ℝ ((callPayoff '' 𝒦) ∪ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)}) :
          Submodule ℝ H_S) = ⊤ ↔
      Submodule.topologicalClosure
        (Submodule.span ℝ {Y I | (I : Word (d + 1)) (_ : I.length ≤ N)} : Submodule ℝ H_S) =
        Submodule.topologicalClosure (Submodule.span ℝ (Set.range Y) : Submodule ℝ H_S))

namespace PriceFiltrationSignatureSpace

def V_subspace {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) : Submodule ℝ H_S := sorry

def V_infty {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d) : Submodule ℝ H_S := sorry

def completenessDepth {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d) : ℕ∞ := sorry

def augmentedMarketSpan {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d) (𝒦 : Set ℝ) (N : ℕ) :
    Submodule ℝ H_S := sorry

def IsCompleteOnPriceFiltration {H_S : Type u_1} [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d) (𝒦 : Set ℝ) (N : ℕ) : Prop := sorry

end PriceFiltrationSignatureSpace

structure GKWDecompositionSetup (H_S : Type u_1) [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S] (d : ℕ) (w : Weight)
    (PFS : PriceFiltrationSignatureSpace H_S d) where
  /-- Closed dynamic-replicable subspace `ℋ_0 := span{1} ⊔ dynamicGainSubspace` (assumed closed by
  Itô/martingale isometry of `L^2(S)`). -/
  replicableSubspace : Submodule ℝ H_S
  replicable_closed : IsClosed (replicableSubspace : Set H_S)
  replicable_hasOrthProj : Submodule.HasOrthogonalProjection replicableSubspace
  /-- Expectation functional `E_ℚ[X]` as an orthogonal projection onto constants. -/
  expectationPart : H_S →L[ℝ] H_S
  /-- Dynamic stochastic integral component `∫_0^T H^X_s dS_s` inside `replicableSubspace`. -/
  stochasticIntegralPart : H_S →L[ℝ] H_S
  /-- Every element in the orthogonal projection onto `replicableSubspace` splits into
  `expectationPart X + stochasticIntegralPart X`. -/
  orthProj_split : ∀ X : H_S,
    @replicableStarProjection H_S _ _ replicableSubspace replicable_hasOrthProj X =
      expectationPart X + stochasticIntegralPart X
  /-- Evaluation map sending a formal series `b ∈ T_{w'}` to the payoff `⟨b, Ŵ_T⟩` projected onto
  `H_S = L^2(ℱ^S_T, ℚ)`, satisfying `‖evalSig b‖_{L^2} ≤ C_sig ‖b‖_{2, w^{-1}}`. -/
  C_sig : ℝ
  hC_sig_nonneg : 0 ≤ C_sig
  evalSig : ExtTensorAlgebra (d + 1) → H_S
  evalSig_add : ∀ a b, evalSig (a + b) = evalSig a + evalSig b
  evalSig_le_in_V : ∀ N : ℕ, ∀ b : ExtTensorAlgebra (d + 1),
    evalSig (projLe N b) ∈ PFS.V_subspace N
  evalSig_l2_bound : ∀ b : ExtTensorAlgebra (d + 1), MemL2wInv w b →
    ‖evalSig b‖ ≤ C_sig * norm2wInv w b

theorem theorem_A {Ω : Type u_1} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      ∀ (S_tilde : ℝ → Ω → ℝ),
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
          S_tilde t ω = M.s₀ + ito.itoInt (fun s ω' => S_tilde s ω' *
              SignatureVolatilityModel.sigma M setup s ω') t ω) →
        ∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 M.T, S_tilde t ω = sol.S t ω := by
  sorry

theorem theorem_B {Ω : Type u_1} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup)
    (ricKit : SignatureRiccatiKit Ω ℙ M setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) ℙ ∧
        ℙ[sol.S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] sol.S s) ∧
      SatisfiesNFLVR ℙ (AdmissibleGainsUnderP ℙ) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale ℙ setup.signatureFiltration M.T
          (fun t ω => (setup.W_hat t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        Nonempty (ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1) →
        ∃ rSol : ClassicalRiccatiSolution M.w M.T ricKit.R_op u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
            ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
              setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (setup.W_hat t ω))) := by
  sorry

theorem theorem_C {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d)
    {𝒦₁ 𝒦₂ : Set ℝ} (h𝒦₁ : Ioi (0 : ℝ) ⊆ closure 𝒦₁) (h𝒦₂ : Ioi (0 : ℝ) ⊆ closure 𝒦₂) :
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞)) ∧
    (∀ M : ℕ, (M : ℕ∞) < PFS.completenessDepth → ¬ PFS.IsCompleteOnPriceFiltration 𝒦₁ M) ∧
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.IsCompleteOnPriceFiltration 𝒦₂ N) := by
  sorry

theorem theorem_D {H_S : Type u_1} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ} {w : Weight}
    {PFS : PriceFiltrationSignatureSpace H_S d}
    (gkw : GKWDecompositionSetup H_S d w PFS) :
    -- (1) Unique orthogonal GKW decomposition & Pythagorean variance formula:
    (∀ X : H_S, ∃ ε_T : H_S,
      X = gkw.expectationPart X + gkw.stochasticIntegralPart X + ε_T ∧
      (∀ Z ∈ gkw.replicableSubspace, ⟪ε_T, Z⟫ = 0) ∧
      ‖X‖ ^ 2 = ‖gkw.expectationPart X + gkw.stochasticIntegralPart X‖ ^ 2 + ‖ε_T‖ ^ 2) ∧
    -- (2) Quantitative weight-ratio tail bound on `𝒲_{w'}`:
    (∀ (w' : Weight) (b : ExtTensorAlgebra (d + 1)) (_hb : MemTw w' b)
        (N : ℕ) (ρ_N : ℝ) (_hρ : 0 ≤ ρ_N),
      (∀ n : ℕ, N < n → w n / w' n ≤ ρ_N) →
      ∃ Z ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N,
        ‖gkw.evalSig b - Z‖ ≤ gkw.C_sig * ρ_N * normW w' b) ∧
    -- (3) Zero residual at or above finite completeness depth `N ≥ N^*_S` (when `𝒱^{(∞)}_S = ⊤`):
    (PFS.V_infty = ⊤ → ∀ N : ℕ, PFS.completenessDepth ≤ (N : ℕ∞) →
      ∀ X : H_S, X ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N) := by
  sorry

end
end SignatureVolatility
