/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module
public import Mathlib
public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Std.Tactic.BVDecide.Normalize.Prop
meta import Lean.Meta.Tactic.AuxLemma
@[expose] public section
set_option warn.classDefReducibility false
noncomputable section
set_option warn.sorry false
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal Topology BigOperators
namespace SignatureVolatility
/-- Admissible terminal gains under `ℙ`: integrable `G` with `𝔼_ℙ[G] ≤ 0`. -/
def AdmissibleGainsUnderP {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) : Set (Ω → ℝ) :=
  {G | Integrable G ℙ ∧ ∫ ω, G ω ∂ℙ ≤ 0}
/-- A weight sequence `w : ℕ → ℝ` with `w 0 = 1`, `w n > 0` for all `n`, and `w` monotone. -/
structure Weight where
  toFun : ℕ → ℝ
  w_zero : toFun 0 = 1
  pos : ∀ n : ℕ, 0 < toFun n
  mono : Monotone toFun
instance : CoeFun Weight (fun _ => ℕ → ℝ) := ⟨Weight.toFun⟩
abbrev Letter (d : ℕ) := Fin d
abbrev Word (d : ℕ) := List (Letter d)
/-- **Definition 2.3 (Extended tensor algebra)**: `T((ℝ^d)) = ∏_{n ≥ 0} (ℝ^d)^{⊗ n}`, represented via word-indexed formal series. -/
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
def wordsOfLength (d : ℕ) : ℕ → Finset (Word d)
  | 0 => {[]}
  | n + 1 =>
    (Finset.univ : Finset (Fin d)).biUnion fun i =>
      (wordsOfLength d n).map ⟨fun I => i :: I, fun _ _ h => (List.cons.inj h).2⟩
namespace wordsOfLength
lemma mem {d : ℕ} {n : ℕ} {I : Word d} : I ∈ wordsOfLength d n ↔ I.length = n := by
  induction n generalizing I with
  | zero =>
    cases I with
    | nil =>
      exact ⟨fun _ => List.length_nil, fun _ => Finset.mem_singleton_self _⟩
    | cons i I =>
      refine ⟨fun h => (List.cons_ne_nil i I (Finset.mem_singleton.mp h)).elim,
        fun hlen => (Nat.succ_ne_zero I.length hlen).elim⟩
  | succ n ih =>
    cases I with
    | nil =>
      refine ⟨fun h => ?_, fun hlen => (Nat.succ_ne_zero n hlen.symm).elim⟩
      rw [wordsOfLength, Finset.mem_biUnion] at h
      obtain ⟨_, _, hmap⟩ := h
      rw [Finset.mem_map] at hmap
      obtain ⟨_, _, hcons⟩ := hmap
      exact (List.cons_ne_nil _ _ hcons).elim
    | cons i I =>
      rw [wordsOfLength, Finset.mem_biUnion]
      constructor
      · intro h
        obtain ⟨j, _, hmap⟩ := h
        rw [Finset.mem_map] at hmap
        obtain ⟨J, hJ, hcons⟩ := hmap
        cases hcons
        exact congrArg Nat.succ (ih.mp hJ)
      · intro hlen
        refine ⟨i, Finset.mem_univ i, ?_⟩
        rw [Finset.mem_map]
        exact ⟨I, ih.mpr (Nat.succ_inj.mp hlen), rfl⟩
end wordsOfLength
namespace ExtTensorAlgebra
/-- Squared Euclidean norm of the level-`n` component: `∑_{|I| = n} a_I²`. -/
def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, (a.coeff I) ^ 2
/-- `a` is finitely supported: all coefficients of words longer than some `N` vanish. -/
def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop :=
  ∃ N : ℕ, ∀ I : Word d, N < I.length → a.coeff I = 0
/-- The basis element `e_I`: coefficient `1` at the word `I` and `0` elsewhere. -/
def basisWord {d : ℕ} (I : Word d) : ExtTensorAlgebra d :=
  ⟨fun J => if J = I then 1 else 0⟩
/-- Euclidean norm of the level-`n` component: `(∑_{|I| = n} a_I²)^{1/2}`. -/
def levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  Real.sqrt (levelNormSq a n)
end ExtTensorAlgebra
/-- `a ∈ T^w`: the weighted level norms are summable, `∑_n w_n ‖a^{(n)}‖ < ∞`. -/
def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => w n * a.levelNorm n)
/-- The weighted norm `‖a‖_w = ∑_n w_n ‖a^{(n)}‖`. -/
def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, w n * a.levelNorm n
/-- `ℓ ∈ ℓ²_w`: `∑_n ‖ℓ^{(n)}‖² / w_n² < ∞`. -/
def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => ℓ.levelNormSq n / (w n) ^ 2)
/-- **Hypothesis H1**: the volatility functional satisfies `ℓ ∈ ℓ²_w`. -/
structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ
lemma hypH1_of_isFinitelySupported {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra (d + 1)}
    (hfin : ExtTensorAlgebra.IsFinitelySupported ℓ) : HypH1 w ℓ := by
  rcases hfin with ⟨N, hN⟩
  refine ⟨summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_⟩
  have hgt : N < n := Nat.lt_of_not_ge fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hl0 : ℓ.levelNormSq n = 0 := by
    unfold ExtTensorAlgebra.levelNormSq
    refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    rw [hN I (hlen ▸ hgt)]
    ring
  rw [hl0, zero_div]
namespace Weight
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl
def geometric (r : ℝ) (hr : 1 ≤ r) : Weight where
  toFun n := r ^ n
  w_zero := pow_zero r
  pos n := pow_pos (zero_lt_one.trans_le hr) n
  mono _ _ hmn := pow_le_pow_right₀ hr hmn
end Weight
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- **Hypothesis H2** (admissible weight): `w (m + n) ≤ C_w w_m w_n` for some `C_w ≥ 1`, and
`∑_n w_n Rⁿ / n! < ∞` for every `R > 0`. -/
structure HypH2 (w : Weight) where
  C_w : ℝ
  one_le_Cw : 1 ≤ C_w
  submult : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n
  subfactorial : ∀ R : ℝ, 0 < R → Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ)))
namespace HypH2
def geometric_admissible (r : ℝ) (hr : 1 ≤ r) : HypH2 (Weight.geometric r hr) where
  C_w := 1
  one_le_Cw := le_rfl
  submult m n := by simp [Weight.geometric, pow_add]
  subfactorial R _ := by
    have hrew : (fun n : ℕ => (Weight.geometric r hr) n * (R ^ n / (n.factorial : ℝ))) =
        fun n : ℕ => (r * R) ^ n / (n.factorial : ℝ) := by
      ext n
      simp [Weight.geometric, mul_pow, mul_div_assoc]
    rw [hrew]
    exact Real.summable_pow_div_factorial (r * R)
def constOne_admissible : HypH2 Weight.constOne where
  C_w := 1
  one_le_Cw := le_rfl
  submult _ _ := by simp [Weight.constOne]
  subfactorial R _ := by
    simpa [Weight.constOne] using Real.summable_pow_div_factorial R
end HypH2
/-- Hypothesis H3: `𝔼[exp(λ ∫₀ᵀ ξ_s² ds)] < ∞` for every `λ > 0`. -/
def HypH3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (ξ : ℝ → Ω → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    Integrable (fun ω => Real.exp (lam * ∫ s in (0 : ℝ)..T, (ξ s ω) ^ 2)) P
/-- Parameter-level remnant used by `SignatureVolatilityModel`: `ℓ` is nontrivial.
The analytic H3 above is imposed separately on `(P, T, ξ)` when building kits. -/
structure HypH3Param {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0
section
open scoped Classical RealInnerProductSpace
/-- A signature volatility model: horizon `T > 0`, weight, `ℓ`, `s₀ > 0`, and H1–H2, `ℓ ≠ 0`. -/
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
  /-- Parameter nondegeneracy (`ℓ ≠ 0`). Analytic Novikov H3 on `ξ = ⟨ℓ,Ŵ⟩` is
  a separate hypothesis when inhabiting `ItoCalculusKit`. -/
  h3 : HypH3Param hd ℓ
end
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The Black–Scholes model as a signature volatility model: `d = 1`, constant weight, and
`ℓ = σ₀ e_∅`, so the volatility is the constant `σ₀ ≠ 0`. -/
def blackScholesModel (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0) :
    SignatureVolatilityModel where
  d := 1
  hd := Nat.succ_pos 0
  T := T
  hT := hT
  w := Weight.constOne
  ℓ := σ₀ • ExtTensorAlgebra.basisWord ([] : Word 2)
  s₀ := s₀
  hs₀ := hs₀
  h1 := hypH1_of_isFinitelySupported Weight.constOne ⟨0, fun I hI => by
    have hne : I ≠ [] := fun h => by subst h; exact Nat.not_lt_zero _ hI
    change σ₀ * (if I = [] then 1 else 0) = 0
    simp [hne]⟩
  h2 := HypH2.constOne_admissible
  h3 := ⟨fun hzero => by
    have hc := congrArg (fun a => a.coeff ([] : Word 2)) hzero
    change σ₀ * (if ([] : Word 2) = [] then (1 : ℝ) else 0) = 0 at hc
    simp at hc
    exact hσ₀ hc⟩
namespace ExtTensorAlgebra
/-- The list (with multiplicity) of all shuffles of the words `I` and `J`. -/
def shuffleWords {d : ℕ} : Word d → Word d → List (Word d)
  | [], J => [J]
  | i :: I, [] => [i :: I]
  | i :: I, j :: J =>
    (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·)
termination_by I J => I.length + J.length
end ExtTensorAlgebra
/-- A real-indexed filtration: σ-algebras `σAlg t`, increasing in `t`, below the ambient one. -/
structure IndexedFiltration (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The filtration generated by the processes `Z · i`: `σAlg t = σ(Z_s i : 0 ≤ s ≤ t, i)`. -/
def generatedFiltration {Ω ι : Type*} [m₀ : MeasurableSpace Ω]
    (Z : ℝ → ι → Ω → ℝ) (hmeas : ∀ t i, Measurable (Z t i)) : IndexedFiltration Ω where
  σAlg t := ⨆ (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (i : ι),
    MeasurableSpace.comap (Z s.1 i) inferInstance
  mono _ _ hst := iSup_le fun u => le_iSup_of_le ⟨u.1, u.2.1, u.2.2.trans hst⟩ le_rfl
  le_ambient _ := iSup_le fun u => iSup_le fun i => (hmeas u.1 i).comap_le
def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Itô–Stratonovich half-Laplacian: `(Δ u)_I = ½ ∑_{i=1}^{d} u_{I i i}` (space letters only). -/
def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩
namespace ExtTensorAlgebra
/-- The shuffle product `e_I ⧢ e_J = ∑_{K ∈ I ⧢ J} e_K` (with multiplicity). -/
def shuffleBasis {d : ℕ} (I J : Word d) : ExtTensorAlgebra d :=
  ⟨fun K => ((shuffleWords I J).map fun L => if K = L then (1 : ℝ) else 0).sum⟩
end ExtTensorAlgebra
/-- The shuffle product `a ⧢ b` restricted to pairs of words `I, J` of length at most
`supportBound`: `∑_{|I|, |J| ≤ supportBound} a_I b_J (e_I ⧢ e_J)`. -/
def shuffleFinite {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (supportBound : ℕ) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun K =>
    ∑ m ∈ Finset.range (supportBound + 1),
      ∑ n ∈ Finset.range (supportBound + 1),
        ∑ I ∈ wordsOfLength (d + 1) m,
          ∑ J ∈ wordsOfLength (d + 1) n,
            a.coeff I * b.coeff J * (ExtTensorAlgebra.shuffleBasis I J).coeff K⟩
/-- A classical solution `ψ` on `[0, T]` of the Riccati equation `ψ' = R(ψ)`, `ψ(0) = u₀`: each
`ψ t ∈ T^w`, uniformly `‖·‖_w`-bounded, with each coefficient satisfying the integral equation
with a continuous integrand. -/
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
namespace ExtTensorAlgebra
/-- Level-`n` inner product `∑_{|I| = n} ℓ_I a_I`. -/
def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, ℓ.coeff I * a.coeff I
end ExtTensorAlgebra
/-- The dual pairing `⟨ℓ, a⟩ = ∑_n ∑_{|I| = n} ℓ_I a_I` (a `tsum` over levels). -/
def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, ℓ.levelInner a n
namespace ExtTensorAlgebra
/-- The free tensor algebra: the finitely supported elements of `T((ℝ^d))`. -/
abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}
end ExtTensorAlgebra
/-- **Special semimartingale on `[0, T]`** (paper Lemma 43): `X = X₀ + M + A` with `M₀ = A₀ = 0`,
`M` an a.s. continuous square-integrable true martingale and `A` an a.s. continuous adapted
finite-variation part of integrable total variation on `[0, T]`. -/
structure IsSpecialSemimartingale {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) (ℱ : IndexedFiltration Ω) (T : ℝ) (X : ℝ → Ω → ℝ) where
  M_part : ℝ → Ω → ℝ
  A_part : ℝ → Ω → ℝ
  decomp : ∀ t ∈ Icc 0 T, ∀ ω, X t ω = X 0 ω + M_part t ω + A_part t ω
  M_zero : ∀ ω, M_part 0 ω = 0
  A_zero : ∀ ω, A_part 0 ω = 0
  M_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    Integrable (M_part t) ℙ ∧ ℙ[M_part t | ℱ.σAlg s] =ᵐ[ℙ] M_part s
  M_l2_bdd : Integrable (fun ω => (M_part T ω) ^ 2) ℙ
  M_cont : ∀ᵐ ω ∂ℙ, ContinuousOn (fun t => M_part t ω) (Icc 0 T)
  A_cont : ∀ᵐ ω ∂ℙ, ContinuousOn (fun t => A_part t ω) (Icc 0 T)
  A_adapted : ∀ t ∈ Icc 0 T, Measurable[ℱ.σAlg t] (A_part t)
  A_integrable_var : ∃ V : Ω → ℝ, Integrable V ℙ ∧
    ∀ᵐ ω ∂ℙ, eVariationOn (fun t => A_part t ω) (Icc 0 T) ≤ ENNReal.ofReal (V ω)
/-- The price filtration `ℱ^S_t = σ(S_u : 0 ≤ u ≤ t)`. -/
def priceFiltration {Ω : Type*} [MeasurableSpace Ω]
    (S : ℝ → Ω → ℝ) (hS_meas : ∀ t, Measurable (S t)) : IndexedFiltration Ω :=
  generatedFiltration (fun t (_ : Unit) ω => S t ω) (fun t _ => hS_meas t)
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Square-integrable envelope of `sup |S_t|` and an `L⁴` Kolmogorov bound on `S σ`. -/
def KitStrongSolutionClass {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) (T : ℝ)
    (σ S : ℝ → Ω → ℝ) : Prop :=
  (∃ S_sup : Ω → ℝ, Measurable S_sup ∧ (∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
  ∃ K : ℝ, 0 ≤ K ∧ (∀ u ∈ Icc 0 T, MemLp (fun ω => S u ω * σ u ω) 4 ℙ) ∧
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      ∫ ω, (S v ω * σ v ω - S u ω * σ u ω) ^ 4 ∂ℙ ≤ K * (v - u) ^ 2
section
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open ExtTensorAlgebra
/-- Paper Definition 18: the global Riccati vector field on `T_w`. -/
def riccatiOp {d : ℕ} (u : ExtTensorAlgebra (d + 1)) : ExtTensorAlgebra (d + 1) :=
  ⟨fun K => (rightShift 0 u + stratonovichHalfLaplacian u).coeff K +
    (1 / 2 : ℝ) * ∑ i : Fin d,
      (shuffleFinite (rightShift i.succ u) (rightShift i.succ u) K.length).coeff K⟩
end
section
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def dyadicFloor (n : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n
variable {Ω : Type*}
def contVersion (X : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => X (dyadicFloor n t) ω
lemma measurable_contVersion {m : MeasurableSpace Ω} (X : ℝ → Ω → ℝ) (t : ℝ)
    (hX : ∀ n, Measurable[m] (X (dyadicFloor n t))) : Measurable[m] (contVersion X t) :=
  haveI : T0Space ℝ := T6Space.toT0Space
  (StronglyMeasurable.limUnder fun n => (hX n).stronglyMeasurable).measurable
end
noncomputable def toNNRealTime (t : ℝ) : ℝ≥0 := Real.toNNReal t
/-- Coordinatewise reindex for `Fin d`-valued drivers. -/
noncomputable def reindexProcessFin {Ω : Type*} {d : ℕ}
    (X : ℝ≥0 → Ω → Fin d → ℝ) : ℝ → Ω → Fin d → ℝ :=
  fun t ω i => X (toNNRealTime t) ω i
lemma measurable_reindexProcessFin {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → Fin d → ℝ} (hX : ∀ t i, Measurable (fun ω => X t ω i))
    (t : ℝ) (i : Fin d) :
    Measurable (fun ω => reindexProcessFin X t ω i) :=
  hX _ _
section
open ProbabilityTheory
/-- A `d`-dimensional Brownian driver on `ℝ≥0` with continuous independent coordinates. -/
structure MultiBrownian (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Coordinate processes on Mathlib time `ℝ≥0`. -/
  Wnn : ℝ≥0 → Ω → Fin d → ℝ
  isBrownian : ∀ i : Fin d, IsBrownianReal (fun t ω => Wnn t ω i) P
  Wnn_zero : ∀ ω i, Wnn 0 ω i = 0
  Wnn_meas : ∀ t i, Measurable (fun ω => Wnn t ω i)
  /-- Paths are continuous at every `ω` (not merely almost every). -/
  pathContinuous : ∀ (i : Fin d) (ω : Ω), Continuous fun t : ℝ≥0 => Wnn t ω i
  /-- Coordinate processes are mutually independent (stronger than fixed-time independence). -/
  coordsIndep : iIndepFun (fun i : Fin d => fun ω => fun t : ℝ≥0 => Wnn t ω i) P
namespace MultiBrownian
/-- Reindexed driver `ℝ → Ω → Fin d → ℝ` (negative times read time `0`). -/
def W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) : ℝ → Ω → Fin d → ℝ :=
  reindexProcessFin B.Wnn
lemma W_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (i : Fin d) :
    Measurable (fun ω => W B t ω i) :=
  measurable_reindexProcessFin B.Wnn_meas t i
end MultiBrownian
end
section
open scoped Interval
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Space increment of coordinate `i` between `ℝ`-times `s` and `t` via `toNNReal`. -/
def wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  B.Wnn (Real.toNNReal t) ω i - B.Wnn (Real.toNNReal s) ω i
lemma measurable_wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) :
    Measurable (fun ω => wnnIncr B i s t ω) :=
  (B.Wnn_meas _ i).sub (B.Wnn_meas _ i)
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Dyadic left Riemann sum for `∫_s^t H_u du`. -/
def lebRiemann_process (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ k ∈ Finset.range (n + 1), H (s + (k : ℝ) * Δ) ω * Δ
lemma measurable_lebRiemann_process (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u))
    (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => lebRiemann_process H s t n ω) :=
  Finset.measurable_sum _ fun _ _ => (hH _).mul measurable_const
/-- Pathwise Lebesgue `∫_s^t H_u du` as dyadic Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def lebIntegral_process (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => lebRiemann_process H s t n ω else 0
lemma measurable_lebIntegral_process (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u))
    (s t : ℝ) :
    Measurable (fun ω => lebIntegral_process H s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [lebIntegral_process, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_lebRiemann_process H hH s t n).stronglyMeasurable)).measurable
  · simp [lebIntegral_process, h]
/-- Dyadic left Itô–Riemann sum for `∫_s^t H_u dW^k`. -/
def itoRiemann_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ j ∈ Finset.range (n + 1),
    H (s + (j : ℝ) * Δ) ω *
      wnnIncr B k (s + (j : ℝ) * Δ) (s + ((j : ℝ) + 1) * Δ) ω
lemma measurable_itoRiemann_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) (n : ℕ) :
    Measurable (fun ω => itoRiemann_process B k H s t n ω) :=
  Finset.measurable_sum _ fun _ _ =>
    (hH _).mul (measurable_wnnIncr B k _ _)
/-- Pathwise Itô `∫_s^t H_u dW^k` as dyadic Itô–Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def itoIntegral_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => itoRiemann_process B k H s t n ω else 0
lemma measurable_itoIntegral_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) :
    Measurable (fun ω => itoIntegral_process B k H s t ω) := by
  classical
  by_cases h : s ≤ t
  · simp only [itoIntegral_process, h, ↓reduceDIte]
    exact (StronglyMeasurable.limUnder
      (fun n => (measurable_itoRiemann_process B k H hH s t n).stronglyMeasurable)).measurable
  · simp [itoIntegral_process, h]
end
section
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Space letter `j : Fin (d+1)` with `j ≠ 0` as a Brownian coordinate index. -/
def spaceLetterIndex (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0) : Fin d :=
  ⟨j.1 - 1, (Nat.sub_lt_iff_lt_add (Nat.one_le_iff_ne_zero.mpr hj)).mpr
    j.isLt⟩
set_option bootstrap.genMatcherCode false in
/-- Level-1 (and empty) Itô coordinates of `wAug`, fully explicit. -/
def itoWordIntegral_le1 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I ≠ [] then 0
    else if h : (j : ℕ) = 0 then t - s
    else
      MultiBrownian.W B t ω (spaceLetterIndex j h) -
        MultiBrownian.W B s ω (spaceLetterIndex j h)
lemma measurable_itoWordIntegral_le1 (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral_le1 B s t ω I) := by
  cases I with
  | nil => simp [itoWordIntegral_le1]
  | cons j I' =>
    simp only [itoWordIntegral_le1]
    by_cases hI : I' ≠ []
    · simp [hI]
    · simp only [hI, ↓reduceIte]
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
      · simp only [hj, ↓reduceDIte]
        exact (MultiBrownian.W_meas B t (spaceLetterIndex j hj)).sub
          (MultiBrownian.W_meas B s (spaceLetterIndex j hj))
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Recursive Itô step for previous words of length `≥ 2`, given as process `H`. -/
def itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if hj : (j : ℕ) = 0 then lebIntegral_process H s t ω
  else itoIntegral_process B (spaceLetterIndex j hj) H s t ω
lemma measurable_itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) :
    Measurable (fun ω => itoWordIntegral_cons_long B j H s t ω) := by
  simp only [itoWordIntegral_cons_long]
  by_cases hj : (j : ℕ) = 0
  · simpa [hj] using measurable_lebIntegral_process H hH s t
  · simpa [hj] using measurable_itoIntegral_process B (spaceLetterIndex j hj) H hH s t
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- One Itô step at upper time `u` for the word `j :: I` (`I ≠ []`), given the previous
coordinate process `H` of `I` (a Lebesgue or Itô–Riemann limit); `0` for `u < s`. -/
def itoWordStep (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (s u : ℝ) (ω : Ω) : ℝ :=
  if s ≤ u then itoWordIntegral_cons_long B j H s u ω else 0
/-- Word-indexed Itô iterated integral of `wAug` over `[s,t]`. Levels `≥ 2` are taken as
their adapted continuous versions (`contVersion`) before being integrated further. -/
def itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I = [] then itoWordIntegral_le1 B s t ω [j]
    else
      contVersion (itoWordStep B j (fun u ω' => itoWordIntegral B s u ω' I) s) t ω
lemma measurable_itoWordStep (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s u : ℝ) :
    Measurable (fun ω => itoWordStep B j H s u ω) := by
  unfold itoWordStep
  by_cases hsu : s ≤ u
  · simpa [hsu] using measurable_itoWordIntegral_cons_long B j H hH s u
  · simp [hsu]
lemma measurable_itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral B s t ω I) := by
  cases I with
  | nil => simp [itoWordIntegral]
  | cons j I' =>
    by_cases hI : I' = []
    · subst hI
      simpa [itoWordIntegral] using measurable_itoWordIntegral_le1 B s t [j]
    · simp only [itoWordIntegral, hI, ↓reduceIte]
      exact measurable_contVersion _ t fun n => measurable_itoWordStep B j _
        (fun u => measurable_itoWordIntegral B s u I') s _
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Weighted contraction list of `I` (paper Appendix). -/
def contractions : Word (d + 1) → List (ℝ × Word (d + 1))
  | [] => [(1, [])]
  | [j] => [(1, [j])]
  | j :: j' :: K =>
      (contractions (j' :: K)).map (fun p => (p.1, j :: p.2)) ++
        (if j = j' ∧ (j : ℕ) ≠ 0 then
          (contractions K).map (fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)) else [])
/-- Combinatorial conversion coefficient `a_{I,J}` (Appendix); empty `Γ` excluded. -/
def stratItoCoeff (I J : Word (d + 1)) : ℝ :=
  (((contractions I).tail.filter (fun p => decide (p.2 = J))).map Prod.fst).sum
/-- Correction polynomial. Vanishes for `|I| ≤ 1`; for longer words, finite sum of
`stratItoCoeff I J * itoWordIntegral … J` over `|J| < |I|`. -/
def stratItoCorrection (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    Word (d + 1) → ℝ
  | [] => 0
  | [_] => 0
  | I@(_ :: _ :: _) =>
      ∑ n ∈ Finset.range I.length,
        ∑ J ∈ wordsOfLength (d + 1) n,
          stratItoCoeff I J * itoWordIntegral B s t ω J
/-- Stratonovich word coordinate via triangular conversion from Itô. -/
def stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (I : Word (d + 1)) : ℝ :=
  itoWordIntegral B s t ω I + stratItoCorrection B s t ω I
lemma measurable_stratItoCorrection (B : MultiBrownian Ω P d) (s t : ℝ)
    (I : Word (d + 1)) :
    Measurable (fun ω => stratItoCorrection B s t ω I) := by
  cases I with
  | nil =>
    change Measurable (fun _ => (0 : ℝ))
    exact measurable_const
  | cons _ I' =>
    cases I' with
    | nil =>
      change Measurable (fun _ => (0 : ℝ))
      exact measurable_const
    | cons _ _ =>
      simp only [stratItoCorrection]
      exact Finset.measurable_sum _ fun _ _ =>
        Finset.measurable_sum _ fun J _ =>
          (measurable_itoWordIntegral B s t J).const_mul _
lemma measurable_stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => stratWordIntegral B s t ω I) :=
  (measurable_itoWordIntegral B s t I).add (measurable_stratItoCorrection B s t I)
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Path filtration of `W` (same generators as `sig_adapted_to_W`). -/
def pathFiltration (B : MultiBrownian Ω P d) : IndexedFiltration Ω :=
  generatedFiltration (fun u i ω => MultiBrownian.W B u ω i) (MultiBrownian.W_meas B)
end

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
def bmCoord (B : MultiBrownian Ω P 1) : ℝ → Ω → ℝ :=
  fun t ω => B.W t ω ⟨0, Nat.succ_pos 0⟩
end
section
open Filter Topology
def predSigma {Ω : Type*} [MeasurableSpace Ω] (σAlg : ℝ → MeasurableSpace Ω) (T : ℝ) :
    MeasurableSpace (ℝ × Ω) :=
  MeasurableSpace.generateFrom
    {S | ∃ (a b : ℝ) (A : Set Ω), 0 ≤ a ∧ a ≤ b ∧ b ≤ T ∧ MeasurableSet[σAlg a] A ∧
      S = Ioc a b ×ˢ A}
def IsPredictableProcess {Ω : Type*} [MeasurableSpace Ω] (σAlg : ℝ → MeasurableSpace Ω)
    (T : ℝ) (H : ℝ → Ω → ℝ) : Prop :=
  Measurable[predSigma σAlg T] (Function.uncurry H)
def SAdmissible {Ω : Type*} [MeasurableSpace Ω] (σAlg : ℝ → MeasurableSpace Ω)
    (P : Measure Ω) (S σ : ℝ → Ω → ℝ) (T : ℝ) (H : ℝ → Ω → ℝ) : Prop :=
  IsPredictableProcess σAlg T H ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s => (H s ω * S s ω * σ s ω) ^ 2) (Icc 0 T) volume)
def IsTerminalBoundedBelow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℝ → Ω → ℝ) (T : ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ ∀ᵐ ω ∂P, -a ≤ V T ω
def IsUniformlyBoundedBelow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℝ → Ω → ℝ) (T : ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, -a ≤ V t ω
def itoRiemannSum {Ω : Type*} (K B : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin (n + 1),
    K (k * t / (n + 1 : ℝ)) ω *
      (B ((k + 1 : ℕ) * t / (n + 1 : ℝ)) ω - B (k * t / (n + 1 : ℝ)) ω)
def IsItoIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B K V : ℝ → Ω → ℝ) (T : ℝ) : Prop :=
  (∀ ω, V 0 ω = 0) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => V t ω) (Icc 0 T)) ∧
  ∀ t ∈ Icc 0 T, TendstoInMeasure P (fun n => itoRiemannSum K B t n) atTop (V t)
def LiteralGains {Ω : Type*} [MeasurableSpace Ω] (σAlg : ℝ → MeasurableSpace Ω)
    (P : Measure Ω) (B S σ : ℝ → Ω → ℝ) (T : ℝ) : Set (Ω → ℝ) :=
  {G | ∃ (H V : ℝ → Ω → ℝ),
    SAdmissible σAlg P S σ T H ∧
    IsItoIntegral P B (fun t ω => H t ω * S t ω * σ t ω) V T ∧
    G = V T}
def TerminalBoundedBelowGains {Ω : Type*} [MeasurableSpace Ω]
    (σAlg : ℝ → MeasurableSpace Ω) (P : Measure Ω) (B S σ : ℝ → Ω → ℝ) (T : ℝ) :
    Set (Ω → ℝ) :=
  {G | ∃ (H V : ℝ → Ω → ℝ) (a : ℝ),
    SAdmissible σAlg P S σ T H ∧
    IsTerminalBoundedBelow P V T a ∧
    IsItoIntegral P B (fun t ω => H t ω * S t ω * σ t ω) V T ∧
    G = V T}
def BoundedBelowGains {Ω : Type*} [MeasurableSpace Ω]
    (σAlg : ℝ → MeasurableSpace Ω) (P : Measure Ω) (B S σ : ℝ → Ω → ℝ) (T : ℝ) :
    Set (Ω → ℝ) :=
  {G | ∃ (H V : ℝ → Ω → ℝ) (a : ℝ),
    SAdmissible σAlg P S σ T H ∧
    IsUniformlyBoundedBelow P V T a ∧
    IsItoIntegral P B (fun t ω => H t ω * S t ω * σ t ω) V T ∧
    G = V T}
def nflvrCone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : Set (Ω → ℝ)) :
    Set (Ω → ℝ) :=
  {g | MemLp g ∞ P ∧ ∃ V ∈ K, ∃ u : Ω → ℝ, (∀ᵐ ω ∂P, 0 ≤ u ω) ∧
    g =ᵐ[P] fun ω => V ω - u ω}
def InWeakStarClosure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Set (Ω → ℝ)) (f : Ω → ℝ) : Prop :=
  MemLp f ∞ P ∧
  ∀ ε > 0, ∀ (gs : Finset (Ω → ℝ)),
    (∀ g ∈ gs, Integrable g P) →
    ∃ h ∈ C, MemLp h ∞ P ∧ ∀ g ∈ gs,
      |∫ ω, (h ω - f ω) * g ω ∂P| < ε
def SatisfiesNFLVR_DS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Set (Ω → ℝ)) : Prop :=
  ∀ f : Ω → ℝ, (∀ᵐ ω ∂P, 0 ≤ f ω) → InWeakStarClosure P (nflvrCone P K) f → f =ᵐ[P] 0
end
section
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open scoped Classical
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Measurable replacement: `H` itself when measurable, else `0`. -/
def forceMeasurable (f : Ω → ℝ) : Ω → ℝ :=
  if Measurable f then f else fun _ => (0 : ℝ)
/-- Pointwise measurable version of a process. -/
def forceMeasurableProcess (H : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun u => forceMeasurable (H u)
/-- Driver index `0` when `0 < d`. -/
def kitDriver (hd : 0 < d) : Fin d := ⟨0, hd⟩
/-- Raw (pre-optional-projection) pathwise Itô integral. -/
def kitItoIntRaw (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if hd : 0 < d then
    itoIntegral_process B (kitDriver hd) (forceMeasurableProcess H) 0 t
  else
    fun _ => 0
/-- Raw quadratic variation `∫₀ᵗ H·H` against the Brownian driver (zero when `d = 0`). -/
def kitQuadVarRaw (_B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if 0 < d then
    lebIntegral_process
      (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') 0 t
  else
    fun _ => 0
/-- Both raw Itô and QV are Bochner-integrable (else the kit pair is zeroed). -/
def kitPairIntegrable (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Prop :=
  Integrable (kitItoIntRaw B H t) P ∧ Integrable (kitQuadVarRaw B H t) P
/-- Pathwise Itô integral: condExp onto the path filtration when the pair is integrable, else `0`. -/
def kitItoInt (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    condExp ((pathFiltration B).σAlg t) P (kitItoIntRaw B H t)
  else
    fun _ => 0
lemma kitItoInt_meas (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitItoInt B H t) := by
  simp only [kitItoInt]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).le_ambient t)).measurable
  · exact measurable_const
/-- Quadratic variation: condExp onto the path filtration when the pair is integrable, else `0`. -/
def kitQuadVar (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    condExp ((pathFiltration B).σAlg t) P (kitQuadVarRaw B H t)
  else
    fun _ => 0
lemma kitQuadVar_meas (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitQuadVar B H t) := by
  simp only [kitQuadVar]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).le_ambient t)).measurable
  · exact measurable_const
end
section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
/-- Paper Stratonovich signature of the time-extended Brownian path (iterated integrals). -/
def paperSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I.reverse⟩
lemma paperSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [] = 1 := by
  simp [paperSig2, stratWordIntegral, itoWordIntegral, stratItoCorrection]
lemma measurable_paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (paperSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral B s t I.reverse
end
section
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
lemma dualPairing_smul_basisWord_nil {d : ℕ} (σ₀ : ℝ) (a : ExtTensorAlgebra d) :
    dualPairing (σ₀ • ExtTensorAlgebra.basisWord ([] : Word d)) a = σ₀ * a.coeff [] := by
  have hcoeff : ∀ I : Word d,
      (σ₀ • ExtTensorAlgebra.basisWord ([] : Word d)).coeff I = if I = [] then σ₀ else 0 := by
    intro I
    change σ₀ * (if I = [] then (1 : ℝ) else 0) = _
    split_ifs <;> simp
  have hlev : ∀ n : ℕ, (σ₀ • ExtTensorAlgebra.basisWord ([] : Word d)).levelInner a n =
      if n = 0 then σ₀ * a.coeff [] else 0 := by
    intro n
    unfold ExtTensorAlgebra.levelInner
    split_ifs with hn
    · subst hn
      rw [Finset.sum_eq_single ([] : Word d)]
      · rw [hcoeff]; simp
      · intro I hI hne; rw [hcoeff, ite_eq_right_iff.mpr (fun h => absurd h hne), zero_mul]
      · intro h; exact absurd (wordsOfLength.mem.mpr (rfl : ([] : Word d).length = 0)) h
    · refine Finset.sum_eq_zero fun I hI => ?_
      have hlen : I.length = n := wordsOfLength.mem.mp hI
      have hne : I ≠ [] := fun h => hn (by rw [← hlen, h, List.length_nil])
      rw [hcoeff, ite_eq_right_iff.mpr (fun h => absurd h hne), zero_mul]
  unfold dualPairing
  simp_rw [hlev]
  exact tsum_ite_eq 0 _
variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)
end
section
open scoped Classical RealInnerProductSpace
/-- **NFLVR** for the given admissible terminal gains: if admissible gains `G_n` with uniformly
vanishing negative parts, integrable with `𝔼 G_n ≤ 0`, converge a.s. to an integrable `f ≥ 0`,
then `f = 0` a.s. -/
def SatisfiesNFLVR {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    (AdmissibleTerminalGains : Set (Ω → ℝ)) : Prop :=
  ∀ (G : ℕ → Ω → ℝ) (f : Ω → ℝ),
    (∀ n, G n ∈ AdmissibleTerminalGains) →
    Integrable f ℙ →
    (∀ ω, 0 ≤ f ω) →
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ω, -ε ≤ G n ω) →
    (∀ n, Integrable (G n) ℙ ∧ ∫ ω, G n ω ∂ℙ ≤ 0) →
    (∀ᵐ ω ∂ℙ, Tendsto (fun n => G n ω) atTop (𝓝 (f ω))) →
    f =ᵐ[ℙ] 0
end
section
open scoped RealInnerProductSpace
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- The signature filtration `ℱ^Ŵ_t = σ(⟨e_I, Ŵ_u⟩ : 0 ≤ u ≤ t, I a word)` generated by the
coordinates of the signature `Ŵ_u = paperSig2 B 0 u` of the time-extended path `(u, W_u)`. -/
def sigFiltration {d : ℕ} (B : MultiBrownian Ω P d) : IndexedFiltration Ω :=
  generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I) (measurable_paperSig2_coeff B 0)
/-- The signature volatility `σ_t = ⟨ℓ, Ŵ_t⟩` of the model `M` driven by `B`. -/
def sigVol (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) (t : ℝ) (ω : Ω) : ℝ :=
  dualPairing M.ℓ (paperSig2 B 0 t ω)
/-- Finite signature transform on `[0, T]` for the initial datum `u₀`:
`𝔼 exp⟨u₀, Ŵ_t⟩ < ∞` for every `t ∈ [0, T]`. -/
def SigTransformFinite {d : ℕ} (B : MultiBrownian Ω P d) (T : ℝ)
    (u₀ : ExtTensorAlgebra (d + 1)) : Prop :=
  ∀ t ∈ Icc 0 T, Integrable (fun ω => Real.exp (dualPairing u₀ (paperSig2 B 0 t ω))) P
/-- Signature-price solution of `dS = S σ dW`, `S_0 = s₀`: a.s. continuous paths on `[0, T]` and a.s. Doléans representation at each time (paper Theorem A). -/
structure IsSignaturePrice (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (S : ℝ → Ω → ℝ) : Prop where
  S_zero : ∀ ω, S 0 ω = M.s₀
  S_meas : ∀ t, Measurable (S t)
  S_adapted : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}), Measurable[(sigFiltration B).σAlg t] (S s.1)
  S_strictly_pos : ∀ t ω, 0 < S t ω
  doleans_repr : (∀ᵐ ω ∂P, ContinuousOn (fun t => S t ω) (Icc 0 M.T)) ∧
    ∀ t ∈ Icc 0 M.T, S t =ᵐ[P] fun ω =>
      M.s₀ * Real.exp (kitItoInt B (sigVol M B) t ω -
        (1 / 2 : ℝ) * kitQuadVar B (sigVol M B) t ω)
  solves_sde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P,
    S t ω = M.s₀ + kitItoInt B (fun s ω' => S s ω' * sigVol M B s ω') t ω
  sup_l2_integrable : ∃ S_sup : Ω → ℝ, Measurable S_sup ∧
    (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 M.T, |S t ω| ≤ S_sup ω) ∧ Integrable (fun ω => (S_sup ω) ^ 2) P
  is_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
    Integrable (S t) P ∧ P[S t | (sigFiltration B).σAlg s] =ᵐ[P] S s
/-- **Paper Theorem A (unwrapped).** Under the analytic H3 hypothesis there is a signature-price
solution `S`, unique (up to modification on `[0, T]`) among adapted strong solutions in
`KitStrongSolutionClass`. -/
theorem theorem_A_unwrapped (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (sigVol M B)) :
    ∃ S : ℝ → Ω → ℝ, IsSignaturePrice M B S ∧
      ∀ S_tilde : ℝ → Ω → ℝ,
        (∀ t ∈ Icc 0 M.T, Measurable[(sigFiltration B).σAlg t] (S_tilde t)) →
        KitStrongSolutionClass P M.T (sigVol M B) S_tilde →
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P,
          S_tilde t ω = M.s₀ + kitItoInt B (fun s ω' => S_tilde s ω' * sigVol M B s ω') t ω) →
        ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P, S_tilde t ω = S t ω := by sorry
/-- **Paper Theorem B, `→` direction (unwrapped).** The signature price is a martingale, the
market satisfies Delbaen–Schachermayer NFLVR for uniformly bounded-below admissible gains,
every signature coordinate is a special semimartingale, and a classical Riccati solution exists whenever the affine transform formula holds. -/
theorem theorem_B_mp_unwrapped (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (sigVol M B)) :
    ∃ S : ℝ → Ω → ℝ, IsSignaturePrice M B S ∧
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (S t) P ∧ P[S t | (sigFiltration B).σAlg s] =ᵐ[P] S s) ∧
      SatisfiesNFLVR_DS P
        (BoundedBelowGains (sigFiltration B).σAlg P
          (fun t ω => B.W t ω (kitDriver M.hd))
          S (sigVol M B) M.T) ∧
      (∀ I : Word (M.d + 1), Nonempty (IsSpecialSemimartingale P (sigFiltration B) M.T
        (fun t ω => (paperSig2 B 0 t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        SigTransformFinite B M.T u₀.1 →
        (∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω)) |
              (sigFiltration B).σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (paperSig2 B 0 t ω))) →
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) := by sorry
/-- **Refutation of the affine/Riccati `←` direction (unwrapped).** -/
theorem not_affine_riccati_duality_mpr_unwrapped (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
      SigTransformFinite B M.T u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω)) |
            (sigFiltration B).σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (paperSig2 B 0 t ω)) := by sorry
/-- **Refutation of the affine/Riccati iff (unwrapped).** -/
theorem not_affine_riccati_duality_unwrapped (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
      SigTransformFinite B M.T u₀.1 →
      ((∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω)) |
              (sigFiltration B).σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (paperSig2 B 0 t ω))) ↔
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1)) := by sorry
/-- **Refutation of the Theorem B `←` direction (unwrapped).** -/
theorem not_theorem_B_mpr_unwrapped (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (sigVol M B)) :
    ¬ ∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
      SigTransformFinite B M.T u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω)) |
            (sigFiltration B).σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (paperSig2 B 0 t ω)) := by sorry
/-- **Refutation of Theorem B as stated (unwrapped).** -/
theorem not_theorem_B_unwrapped (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (sigVol M B)) :
    ¬ ∃ S : ℝ → Ω → ℝ, IsSignaturePrice M B S ∧
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (S t) P ∧ P[S t | (sigFiltration B).σAlg s] =ᵐ[P] S s) ∧
      SatisfiesNFLVR_DS P
        (BoundedBelowGains (sigFiltration B).σAlg P
          (fun t ω => B.W t ω (kitDriver M.hd))
          S (sigVol M B) M.T) ∧
      (∀ I : Word (M.d + 1), Nonempty (IsSpecialSemimartingale P (sigFiltration B) M.T
        (fun t ω => (paperSig2 B 0 t ω).coeff I))) ∧
      (∀ u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1),
        SigTransformFinite B M.T u₀.1 →
        ((∃ rSol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
          ∀ t ∈ Icc 0 M.T,
            Integrable (fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω))) P ∧
            P[fun ω => Real.exp (dualPairing u₀.1 (paperSig2 B 0 M.T ω)) |
              (sigFiltration B).σAlg t] =ᵐ[P]
              fun ω => Real.exp (dualPairing (rSol.ψ (M.T - t)) (paperSig2 B 0 t ω))) ↔
        Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1))) := by sorry
/-- The signature price `S_t = s₀ exp(∫_0^t σ dW - ½ ∫_0^t σ² ds)` (the Doléans exponential of
Theorem A), with the Itô integral `kitItoInt B` and quadratic variation `kitQuadVar B`. -/
def sigPrice (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) (t : ℝ) (ω : Ω) : ℝ :=
  M.s₀ * Real.exp (kitItoInt B (sigVol M B) t ω - (1 / 2 : ℝ) * kitQuadVar B (sigVol M B) t ω)
lemma sigPrice_meas (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) (t : ℝ) :
    Measurable (sigPrice M B t) :=
  measurable_const.mul ((kitItoInt_meas B _ t).sub
    (measurable_const.mul (kitQuadVar_meas B _ t))).exp
/-- Market data for Theorems C–D (unwrapped): the model, its Brownian driver, and the analytic
H3 hypothesis of Theorem A. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] where
  M : SignatureVolatilityModel
  B : MultiBrownian Ω P M.d
  h3 : HypH3 P M.T (sigVol M B)
namespace Market
/-- The signature price `S = sigPrice M B` of the market. -/
def S (mkt : Market Ω P) : ℝ → Ω → ℝ := sigPrice mkt.M mkt.B
/-- The price filtration `ℱ^S_t = σ(S_u : 0 ≤ u ≤ t)`. -/
def F_S (mkt : Market Ω P) : IndexedFiltration Ω :=
  priceFiltration mkt.S (sigPrice_meas mkt.M mkt.B)
/-- The constant payoff `1 ∈ L²(ℙ)`. -/
def oneLp (P : Measure Ω) [IsProbabilityMeasure P] : Lp ℝ 2 P :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)
/-- `L²(ℱ^S_T, ℙ)` as a closed subspace of `L²(ℙ)`. -/
def L2S (mkt : Market Ω P) : Submodule ℝ (Lp ℝ 2 P) :=
  lpMeas ℝ ℝ (mkt.F_S.σAlg mkt.M.T) 2 P
/-- Square-integrable stochastic integrals against `S`: `∫_0^T H_s S_s σ_s dW_s` with `H`
adapted to `ℱ^S`, lying in `L²(ℱ^S_T)`. -/
def gainsSet (mkt : Market Ω P) : Set (Lp ℝ 2 P) :=
  {X | X ∈ mkt.L2S ∧ ∃ H : ℝ → Ω → ℝ, (∀ t, Measurable[mkt.F_S.σAlg t] (H t)) ∧
    (X : Ω → ℝ) =ᵐ[P] kitItoInt mkt.B
      (fun s ω => H s ω * mkt.S s ω * sigVol mkt.M mkt.B s ω) mkt.M.T}
/-- **Definition 65.** `H0`, the closed span of the constant `1` and the gains `gainsSet`. -/
def H0 (mkt : Market Ω P) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (insert (Market.oneLp P) mkt.gainsSet)).topologicalClosure
/-- Terminal signature coordinate `⟨e_I, Ŵ_T⟩` as an `L²` class (or `0`). -/
def coord (mkt : Market Ω P) (I : Word (mkt.M.d + 1)) : Lp ℝ 2 P :=
  haveI := Classical.dec (MemLp (fun ω => (paperSig2 mkt.B 0 mkt.M.T ω).coeff I) 2 P)
  if h : MemLp (fun ω => (paperSig2 mkt.B 0 mkt.M.T ω).coeff I) 2 P then h.toLp _ else 0
/-- The depth-`≤ N` terminal signature coordinates `{⟨e_I, Ŵ_T⟩ : |I| ≤ N}` in `L²(ℙ)`. -/
def coordSet (mkt : Market Ω P) (N : ℕ) : Set (Lp ℝ 2 P) :=
  {f | ∃ I : Word (mkt.M.d + 1), I.length ≤ N ∧ f = mkt.coord I}
/-- **Definition 55.** The completeness depth `N^*_S`: the least `N` with
`closure span {⟨e_I, Ŵ_T⟩ : |I| ≤ N} ∩ L²(ℱ^S_T) = L²(ℱ^S_T)`, and `⊤` if there is none. -/
def completenessDepth (mkt : Market Ω P) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ n : ℕ, K = (n : ℕ∞) ∧
    (Submodule.span ℝ (mkt.coordSet n)).topologicalClosure ⊓ mkt.L2S = mkt.L2S}
end Market
/-- **Paper Theorem D / Theorem 66, GKW part (unwrapped).** Every `X ∈ L²(ℱ^S_T)` splits uniquely
as `X = 𝔼X + G + ε` with `G ∈ H0`, `G ⟂ 1`, `ε ∈ L²(ℱ^S_T)`, `ε ⟂ H0` and `ε` orthogonal to all
gains, with the Pythagorean identity. -/
theorem theorem_D_unwrapped (mkt : Market Ω P) (X : Lp ℝ 2 P) (hX : X ∈ mkt.L2S) :
    ∃ G ε : Lp ℝ 2 P,
      G ∈ mkt.H0 ∧ ⟪G, Market.oneLp P⟫ = 0 ∧ ε ∈ mkt.L2S ∧ ε ∈ mkt.H0ᗮ ∧
      (∀ Z ∈ mkt.gainsSet, ⟪ε, Z⟫ = 0) ∧
      X = (∫ ω, X ω ∂P) • Market.oneLp P + G + ε ∧
      ‖X‖ ^ 2 = ‖(∫ ω, X ω ∂P) • Market.oneLp P + G‖ ^ 2 + ‖ε‖ ^ 2 ∧
      ∀ (c : ℝ) (G' ε' : Lp ℝ 2 P), G' ∈ mkt.H0 → ⟪G', Market.oneLp P⟫ = 0 →
        ε' ∈ mkt.H0ᗮ → X = c • Market.oneLp P + G' + ε' →
          c = ∫ ω, X ω ∂P ∧ G' = G ∧ ε' = ε := by sorry
section BlackScholes
variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)
lemma sigVol_blackScholes (B : MultiBrownian Ω P 1) (t : ℝ) (ω : Ω) :
    sigVol (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) B t ω = σ₀ := by
  unfold sigVol blackScholesModel
  have h := dualPairing_smul_basisWord_nil σ₀ (paperSig2 B 0 t ω)
  have h1 : (paperSig2 B 0 t ω).coeff [] = 1 := paperSig2_empty B 0 t ω
  rw [h1, mul_one] at h
  exact h
lemma hypH3_blackScholes (B : MultiBrownian Ω P 1) :
    HypH3 P T (sigVol (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) B) := by
  intro _ _
  have hσ : sigVol (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) B = fun _ _ => σ₀ :=
    funext fun t => funext fun ω => sigVol_blackScholes T s₀ σ₀ hT hs₀ hσ₀ B t ω
  simp only [hσ]
  exact integrable_const _
/-- The Black–Scholes market (constant volatility `σ₀`) on a one-dimensional Brownian driver. -/
def bsMarket (B : MultiBrownian Ω P 1) : Market Ω P :=
  ⟨blackScholesModel T s₀ σ₀ hT hs₀ hσ₀, B, hypH3_blackScholes T s₀ σ₀ hT hs₀ hσ₀ B⟩
/-- **Theorem D residual hypothesis fails (unwrapped).** For Black–Scholes, `N^*_S = ∞`. -/
theorem theorem_D_residual_hypothesis_fails_unwrapped (B : MultiBrownian Ω P 1) :
    ¬ (bsMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤ := by sorry
end BlackScholes
section Completeness
variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)
/-- Elementary Brownian gains on `[0, T]`: the finite sums `∑_{p ∈ V} h_p (W_{p.2} - W_{p.1})`
over time intervals `p.1 ≤ p.2 ≤ T`, where each `h_p` is bounded and measurable for
`σ(W_u : u ≤ p.1)`. -/
def elemGains (B : MultiBrownian Ω P 1) : Set (Lp ℝ 2 P) :=
  {G | ∃ (V : Finset (ℝ≥0 × ℝ≥0)) (h : ℝ≥0 × ℝ≥0 → Ω → ℝ),
    (∀ p ∈ V, p.1 ≤ p.2 ∧ (p.2 : ℝ) ≤ T ∧
      Measurable[⨆ u ≤ p.1, MeasurableSpace.comap (fun ω => B.Wnn u ω 0) inferInstance] (h p) ∧
      ∃ C : ℝ, ∀ ω, |h p ω| ≤ C) ∧
    (G : Ω → ℝ) =ᵐ[P] fun ω => ∑ p ∈ V, h p ω * (B.Wnn p.2 ω 0 - B.Wnn p.1 ω 0)}
/-- Completeness with finitely many calls (Theorem C, unwrapped). -/
def IsCompleteWithCallsUnwrapped (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) : Prop :=
  ∀ X : Lp ℝ 2 P, X ∈ (bsMarket T s₀ σ₀ hT hs₀ hσ₀ B).L2S →
    ∃ (c : ℝ) (a : ℝ → ℝ), ∃ G ∈ (Submodule.span ℝ (elemGains T B)).topologicalClosure,
      (X : Ω → ℝ) =ᵐ[P] fun ω => c +
        ∑ k ∈ strikes, a k * max ((bsMarket T s₀ σ₀ hT hs₀ hσ₀ B).S T ω - k) 0 + G ω
/-- **Refutation of Theorem C (unwrapped).** For the Black–Scholes market and any finite set of
call strikes, "complete with calls ⇔ `N^*_S < ∞`" is false: the market is complete but
`N^*_S = ∞`. -/
theorem not_theorem_C_unwrapped (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    ¬ (IsCompleteWithCallsUnwrapped T s₀ σ₀ hT hs₀ hσ₀ B strikes ↔
      (bsMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤) := by sorry
/-- Literal NFLVR fails for unwrapped Black–Scholes. -/
theorem not_literal_nflvr_unwrapped (B : MultiBrownian Ω P 1) :
    ¬ SatisfiesNFLVR_DS P
        (LiteralGains (pathFiltration B).σAlg P (bmCoord B)
          (sigPrice (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) B)
          (fun _ _ => σ₀) T) := by sorry
/-- Terminal-only bounded-below NFLVR also fails in the unwrapped Black–Scholes market. -/
theorem not_terminal_bdd_nflvr_unwrapped (B : MultiBrownian Ω P 1) :
    ¬ SatisfiesNFLVR_DS P
        (TerminalBoundedBelowGains (pathFiltration B).σAlg P (bmCoord B)
          (sigPrice (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) B)
          (fun _ _ => σ₀) T) := by sorry
end Completeness
end
end SignatureVolatility
end
end
