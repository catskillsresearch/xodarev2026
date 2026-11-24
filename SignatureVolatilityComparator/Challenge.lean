/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Function.L2Space
public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Star
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Data.Set.FiniteExhaustion
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.EMetricSpace.PairReduction
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.CondVar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
meta import Lean.Meta.Tactic.AuxLemma

/-!
# Palomar Challenge (statement of record)

GENERATED by `scripts/gen_challenge.py` (run `scripts/gen_challenge.sh`); do not edit by hand.
Imports only Mathlib. Every declaration the compared statements depend on is copied verbatim
from `SignatureVolatility/` and from the vendored `MathFin` / `BrownianMotion` libraries, each
source module in its own section; the compared theorems (`comparator.json` `theorem_names`)
have their proofs replaced by `sorry`. See `COMPARATOR.md` for what each compared theorem says
about the paper (proved, refuted, or counterexample) and for the one open problem
(`affine_riccati_duality`, outside the submitted library).
-/

set_option warn.sorry false

/-! Lean caches auxiliary `_proof_N` lemmas per file (`Lean.Meta.mkAuxLemma`, cache not stored in
.olean files). In the Solution each source module starts with an empty cache; here all modules
share one file, so each section below first empties that cache. This adds no declarations and
only makes auxiliary proof names match the Solution exactly, as Comparator compares bodies. -/

section
-- source module: SignatureVolatility.AdmissibleGainsUnderP
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.AdmissibleGainsUnderP` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

def AdmissibleGainsUnderP {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) : Set (Ω → ℝ) :=
  {G | Integrable G ℙ ∧ ∫ ω, G ω ∂ℙ ≤ 0}

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.Weight
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Weight` -/
@[expose] public section

namespace SignatureVolatility

structure Weight where
  toFun : ℕ → ℝ
  w_zero : toFun 0 = 1
  pos : ∀ n : ℕ, 0 < toFun n
  mono : Monotone toFun

instance : CoeFun Weight (fun _ => ℕ → ℝ) := ⟨Weight.toFun⟩

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.Letter
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Letter` -/
@[expose] public section

namespace SignatureVolatility

abbrev Letter (d : ℕ) := Fin d

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.Word
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Word` -/
@[expose] public section

namespace SignatureVolatility

abbrev Word (d : ℕ) := List (Letter d)

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra` -/
@[expose] public section

namespace SignatureVolatility

/-- **Definition 2.3 (Extended tensor algebra)**: `T((ℝ^d)) = ∏_{n ≥ 0} (ℝ^d)^{⊗ n}`,
represented via word-indexed formal series. -/
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

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.WordsOfLength
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.WordsOfLength` -/
@[expose] public section

namespace SignatureVolatility

def wordsOfLength (d : ℕ) : ℕ → Finset (Word d)
  | 0 => {[]}
  | n + 1 =>
    (Finset.univ : Finset (Fin d)).biUnion fun i =>
      (wordsOfLength d n).map ⟨fun I => i :: I, fun _ _ h => (List.cons.inj h).2⟩

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.LevelNormSq
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.LevelNormSq` -/
@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, (a.coeff I) ^ 2

end ExtTensorAlgebra

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported` -/
@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop :=
  ∃ N : ℕ, ∀ I : Word d, N < I.length → a.coeff I = 0

end ExtTensorAlgebra

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.BasisWord
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.BasisWord` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def basisWord {d : ℕ} (I : Word d) : ExtTensorAlgebra d :=
  ⟨fun J => if J = I then 1 else 0⟩

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.Concat
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.Concat` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def concat {d : ℕ} (a b : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => ∑ k ∈ Finset.range (I.length + 1), a.coeff (I.take k) * b.coeff (I.drop k)⟩

infixl:70 " ⊗ₜ " => concat

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.LevelNorm
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.LevelNorm` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  Real.sqrt (levelNormSq a n)

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.MemTw
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.MemTw` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => w n * a.levelNorm n)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.NormW
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.NormW` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, w n * a.levelNorm n

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.MemL2w
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.MemL2w` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => ℓ.levelNormSq n / (w n) ^ 2)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.HypH1
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.HypH1` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.HypH1OfIsFinitelySupported
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.HypH1OfIsFinitelySupported` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

lemma hypH1_of_isFinitelySupported {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra (d + 1)}
    (hfin : ExtTensorAlgebra.IsFinitelySupported ℓ) : HypH1 w ℓ := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.Weight.ConstOne
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Weight.ConstOne` -/
@[expose] public section

namespace SignatureVolatility

namespace Weight

def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl

end Weight

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.Weight.Geometric
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Weight.Geometric` -/
@[expose] public section

namespace SignatureVolatility

namespace Weight

def geometric (r : ℝ) (hr : 1 ≤ r) : Weight where
  toFun n := r ^ n
  w_zero := pow_zero r
  pos n := pow_pos (zero_lt_one.trans_le hr) n
  mono _ _ hmn := pow_le_pow_right₀ hr hmn

end Weight

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.HypH2
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.HypH2` -/
@[expose] public section

namespace SignatureVolatility

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

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.HypH3
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.HypH3` -/
@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Hypothesis H3** (paper): for every `λ > 0`,
`𝔼[exp(λ ∫₀ᵀ ξ_s² ds)] < ∞`, where `ξ` is the signature-volatility integrand.
This is the Novikov / exponential-integrability input to the square-integrable
stochastic-exponential construction (not the obsolete `ℓ ≠ 0` stub). -/
def HypH3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (ξ : ℝ → Ω → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    Integrable (fun ω => Real.exp (lam * ∫ s in (0 : ℝ)..T, (ξ s ω) ^ 2)) P

/-- Parameter-level remnant used by `SignatureVolatilityModel`: `ℓ` is nontrivial.
The analytic H3 above is imposed separately on `(P, T, ξ)` when building kits. -/
structure HypH3Param {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.SignatureVolatilityModel
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignatureVolatilityModel` -/
@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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


end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.BlackScholesModel
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.BlackScholesModel` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.ShuffleWords
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.ShuffleWords` -/
@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def shuffleWords {d : ℕ} : Word d → Word d → List (Word d)
  | [], J => [J]
  | i :: I, [] => [i :: I]
  | i :: I, j :: J =>
    (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·)
termination_by I J => I.length + J.length

end ExtTensorAlgebra

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def evalShuffleBasis {d : ℕ} (I J : Word d) (X : ExtTensorAlgebra d) : ℝ :=
  ((shuffleWords I J).map fun K => X.coeff K).sum

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.IndexedFiltration
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.IndexedFiltration` -/
@[expose] public section

namespace SignatureVolatility

structure IndexedFiltration (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.GeneratedFiltration
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.GeneratedFiltration` -/
@[expose] public section

namespace SignatureVolatility

def generatedFiltration {Ω ι : Type*} [m₀ : MeasurableSpace Ω]
    (Z : ℝ → ι → Ω → ℝ) (hmeas : ∀ t i, Measurable (Z t i)) : IndexedFiltration Ω where
  σAlg t := ⨆ (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (i : ι),
    MeasurableSpace.comap (Z s.1 i) inferInstance
  mono _ _ hst := iSup_le fun u => le_iSup_of_le ⟨u.1, u.2.1, u.2.2.trans hst⟩ le_rfl
  le_ambient _ := iSup_le fun u => iSup_le fun i => (hmeas u.1 i).comap_le

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-- Coordinate `j` of the time-extended path `X_t = (t, W_t)`: `X⁰_t = t`, `X^{i+1}_t = W^i_t`. -/
def augCoord {Ω : Type*} {d : ℕ} (W : ℝ → Ω → Fin d → ℝ) (t : ℝ) (ω : Ω) (j : Fin (d + 1)) :
    ℝ :=
  Fin.cases (motive := fun _ => ℝ) t (fun i => W t ω i) j

/-- Trapezoid (Stratonovich) Riemann sum `∑ₖ ½ (Y_{t_k} + Y_{t_{k+1}}) (X^j_{t_{k+1}} - X^j_{t_k})`
on the uniform grid `t_k = k t / (n + 1)`, `k = 0, …, n`. -/
def trapezoidSum {Ω : Type*} {d : ℕ} (W : ℝ → Ω → Fin d → ℝ) (Y : ℝ → Ω → ℝ)
    (j : Fin (d + 1)) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (1 / 2 : ℝ) * (Y (k * t / (n + 1)) ω + Y ((k + 1) * t / (n + 1)) ω) *
      (augCoord W ((k + 1) * t / (n + 1)) ω j - augCoord W (k * t / (n + 1)) ω j)

structure ProlongedBrownianSetup (Ω : Type*) [m₀ : MeasurableSpace Ω]
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
  /-- Multiplicative rough-path/Stratonovich simplex decomposition over `[0, s] ∪ [s, t]`
  (almost surely: iterated stochastic integrals are only defined up to null sets). -/
  stratonovich_chen : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
    ∀ᵐ ω ∂ℙ, sig2 0 t ω = sig2 0 s ω ⊗ₜ sig2 s t ω
  /-- Product-of-simplices Stratonovich shuffle relation on coordinates (almost surely). -/
  stratonovich_shuffle : ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    ∀ (I J : Word (d + 1)), ∀ᵐ ω ∂ℙ,
      (sig2 0 t ω).coeff I * (sig2 0 t ω).coeff J =
        ExtTensorAlgebra.evalShuffleBasis I J (sig2 0 t ω)
  /-- Paper's defining dynamics `dŴ_t = Ŵ_t ⊗ ∘dX_t` (last letter latest): coordinatewise,
  `⟨e_{Ij}, Ŵ_t⟩ = ∫₀ᵗ ⟨e_I, Ŵ_s⟩ ∘dX^j_s`, the Stratonovich integral being the limit in
  probability of trapezoid sums on uniform grids. This pins `sig2` to the signature of
  `X = (t, W_t)`. -/
  stratonovich_dynamics : ∀ (I : Word (d + 1)) (j : Fin (d + 1)) ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
    TendstoInMeasure ℙ (fun n => trapezoidSum W (fun s ω => (sig2 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (sig2 0 t ω).coeff (I ++ [j]))
  /-- Appendix A / paper Proposition 12 factorial level control: for each `p ≥ 1` and any
  nonnegative weight sequence of at most geometric growth `w_n ≤ r^n` (as supplied by `HypH2`
  via submultiplicativity), the weighted level series of `sig2 0 t` converges almost surely and
  lies in `L^p`. Weaker all-radius `R^n/n!` summability is insufficient for Gaussian drivers. -/
  factorial_moment_control : ∀ (p : ℝ), 1 ≤ p →
    ∀ (w_fn : ℕ → ℝ), (∀ n, 0 ≤ w_fn n) →
      (∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n) →
      ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ T →
        (∀ᵐ ω ∂ℙ, Summable (fun n : ℕ => w_fn n * (sig2 0 t ω).levelNorm n)) ∧
        Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2 0 t ω).levelNorm n) ^ p) ℙ

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.RightShift
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.RightShift` -/
@[expose] public section

namespace SignatureVolatility

def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.StratonovichHalfLaplacian
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.StratonovichHalfLaplacian` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.ShuffleBasis
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.ShuffleBasis` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def shuffleBasis {d : ℕ} (I J : Word d) : ExtTensorAlgebra d :=
  ⟨fun K => ((shuffleWords I J).map fun L => if K = L then (1 : ℝ) else 0).sum⟩

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ShuffleFinite
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ShuffleFinite` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def shuffleFinite {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (supportBound : ℕ) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun K =>
    ∑ m ∈ Finset.range (supportBound + 1),
      ∑ n ∈ Finset.range (supportBound + 1),
        ∑ I ∈ wordsOfLength (d + 1) m,
          ∑ J ∈ wordsOfLength (d + 1) n,
            a.coeff I * b.coeff J * (ExtTensorAlgebra.shuffleBasis I J).coeff K⟩

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ClassicalRiccatiSolution
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ClassicalRiccatiSolution` -/
@[expose] public section

noncomputable section

open Set

namespace SignatureVolatility

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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.LevelInner
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.LevelInner` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, ℓ.coeff I * a.coeff I

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.DualPairing
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.DualPairing` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, ℓ.levelInner a n

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.WHat
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.WHat` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def W_hat (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) :
    ExtTensorAlgebra (d + 1) :=
  setup.sig2 0 t ω

end ProlongedBrownianSetup

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.Norm2w
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Norm2w` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

def norm2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, ℓ.levelNormSq n / (w n) ^ 2)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.SignatureVolatilityModel.Sigma
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignatureVolatilityModel.Sigma` -/
@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

namespace SignatureVolatilityModel

def sigma {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (t : ℝ) (ω : Ω) : ℝ :=
  dualPairing M.ℓ (setup.W_hat t ω)

end SignatureVolatilityModel

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

end ExtTensorAlgebra

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.IsSpecialSemimartingale
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.IsSpecialSemimartingale` -/
@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

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

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.PriceFiltration
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.PriceFiltration` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

def priceFiltration {Ω : Type*} [MeasurableSpace Ω]
    (S : ℝ → Ω → ℝ) (hS_meas : ∀ t, Measurable (S t)) : IndexedFiltration Ω :=
  generatedFiltration (fun t (_ : Unit) ω => S t ω) (fun t _ => hS_meas t)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration` -/
@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def signatureFiltration (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω :=
  generatedFiltration (fun u I ω => (setup.W_hat u ω).coeff I) (setup.sig_meas 0)

end ProlongedBrownianSetup

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit` -/
@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Kit strong-solution class.** The kit's stand-in for the paper's strong solutions of
`dS = S σ dW` on `[0, T]` (used together with adaptedness to the signature filtration):

* a square-integrable envelope of `sup_{t ∈ [0,T]} |S_t|` (the paper's `L²` solution class), and
* the SDE integrand `S σ` is `L⁴` with a Kolmogorov-type bound `𝔼 (S_v σ_v - S_u σ_u)⁴ ≤ K (v - u)²`
  on `[0, T]`.

The second clause is the minimal time regularity under which the kit's Riemann-sum integral
`itoInt` is a genuine (linear, martingale, `L²`) Itô integral of `S σ`; every strong solution of
the linear signature SDE under H1–H3 has it (BDG), and the constructed Doléans solution is proved to
have it (`doleans_strong_class`). Without such a class, uniqueness for the kit equation is not
provable: `itoInt` only samples the integrand at the grid points `q t`, `q ∈ ℚ`, and returns `0`
for integrands whose pair is not integrable, so arbitrary adapted processes are not semimartingale
solutions in the paper's sense. -/
def KitStrongSolutionClass {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) (T : ℝ)
    (σ S : ℝ → Ω → ℝ) : Prop :=
  (∃ S_sup : Ω → ℝ, Measurable S_sup ∧ (∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
  ∃ K : ℝ, 0 ≤ K ∧ (∀ u ∈ Icc 0 T, MemLp (fun ω => S u ω * σ u ω) 4 ℙ) ∧
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      ∫ ω, (S v ω * σ v ω - S u ω * σ u ω) ^ 4 ∂ℙ ≤ K * (v - u) ^ 2

/-- Itô calculus kit. Uniqueness is stated up to **modification** (not indistinguishability),
matching SDE hypotheses that constrain each fixed time only almost surely. Novikov/Doob
requires the paper's exponential-integrability hypothesis `HypH3` on the integrand `σ`. -/
structure ItoCalculusKit (Ω : Type*) [m₀ : MeasurableSpace Ω]
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
  /-- Doléans SDE for the signature volatility `σ = ⟨ℓ, Ŵ⟩` under H1–H3, with pathwise
  square-integrability and pathwise continuity of `σ` on `[0, T]`. The statement is restricted
  to this adapted class (as in the two fields below) because it is false for arbitrary `σ`:
  null-set spikes, anticipating integrands and integrands violating H3 are counterexamples. -/
  doleans_sde : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 ℙ T σ →
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    (∀ᵐ ω ∂ℙ, ContinuousOn (fun s => σ s ω) (Icc 0 T)) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ,
      s₀ * doleansExp σ t ω = s₀ + itoInt (fun s ω' => (s₀ * doleansExp σ s ω') * σ s ω') t ω
  /-- L² localisation / Gronwall package under H1–H3. Conclusion is uniqueness **up to
  modification** among strong solutions: adapted to the signature filtration and in
  `KitStrongSolutionClass` (square-integrable supremum, `L⁴`-regular integrand `S σ`). Without
  H1–H2 the volatility can violate every moment bound (e.g. `σ = exp(W⁴)`), in which case
  `itoInt` returns `0` and the constant `s₀` is a spurious solution; without the class, arbitrary
  adapted processes are not semimartingale solutions and uniqueness is not provable. -/
  stopped_l2_localisation : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (S₁ S₂ : ℝ → Ω → ℝ),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 ℙ T σ →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₁ t)) →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₂ t)) →
    KitStrongSolutionClass ℙ T σ S₁ →
    KitStrongSolutionClass ℙ T σ S₂ →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = s₀ + itoInt (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₂ t ω = s₀ + itoInt (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) →
        ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = S₂ t ω))
  /-- Novikov–Doob L² martingale package under H1–H2 and the analytic H3 on `σ`. -/
  novikov_doob_l2_martingale : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * doleansExp σ t ω
    HypH3 ℙ T σ →
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) ℙ ∧
      ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)
  /-- The Doléans price `s₀ · doleansExp σ` lies in the strong-solution class under H1–H3, so the
  uniqueness clause of `stopped_l2_localisation` applies to it. -/
  doleans_strong_class : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 ℙ T σ →
    KitStrongSolutionClass ℙ T σ (fun t ω => s₀ * doleansExp σ t ω)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.SignatureRiccatiKit.RiccatiOp
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignatureRiccatiKit.RiccatiOp` -/
@[expose] public section

noncomputable section

namespace SignatureVolatility

open ExtTensorAlgebra

/-- Paper Definition 18: the global Riccati vector field on `T_w`. -/
def riccatiOp {d : ℕ} (u : ExtTensorAlgebra (d + 1)) : ExtTensorAlgebra (d + 1) :=
  ⟨fun K => (rightShift 0 u + stratonovichHalfLaplacian u).coeff K +
    (1 / 2 : ℝ) * ∑ i : Fin d,
      (shuffleFinite (rightShift i.succ u) (rightShift i.succ u) K.length).coeff K⟩

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.Lemma77ShuffleEstimateFalse
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Lemma77ShuffleEstimateFalse` -/
@[expose] public section


namespace SignatureVolatility

open ExtTensorAlgebra

/-- **Paper Lemma 77 is false** for every weight, in particular for every H2 weight: already on
basis words there is no constant `C` with `‖e_I ⧢ e_J‖_w ≤ C ‖e_I‖_w ‖e_J‖_w`. -/
theorem not_lemma77_shuffle_estimate {d : ℕ} (w : Weight) (l : Fin d) :
    ¬ ∃ C : ℝ, ∀ I J : Word d,
      normW w (shuffleBasis I J) ≤ C * normW w (basisWord I) * normW w (basisWord J) := by
  sorry
/-- Lemma 77 fails for every H2 weight (the hypothesis of the paper's statement). -/
theorem not_lemma77_of_hypH2 {d : ℕ} (w : Weight) (_hw : HypH2 w) (l : Fin d) :
    ¬ ∃ C : ℝ, ∀ I J : Word d,
      normW w (shuffleBasis I J) ≤ C * normW w (basisWord I) * normW w (basisWord J) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.Lemma78RiccatiLipschitzFalse
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Lemma78RiccatiLipschitzFalse` -/
@[expose] public section

namespace SignatureVolatility

open ExtTensorAlgebra

/-- **Paper Lemma 78 is false**: for the H2 weight `w ≡ 1` and at least one space dimension, the
Riccati operator `ℛ` is not locally Lipschitz on bounded subsets of `T_w` (it is not even bounded
on the unit ball). -/
theorem not_lemma78_local_lipschitz {d : ℕ} :
    ¬ ∀ ρ : ℝ, 0 < ρ → ∃ L : ℝ, ∀ u v : ExtTensorAlgebra (d + 2),
      MemTw Weight.constOne u → MemTw Weight.constOne v →
      normW Weight.constOne u ≤ ρ → normW Weight.constOne v ≤ ρ →
      MemTw Weight.constOne (riccatiOp u - riccatiOp v) ∧
        normW Weight.constOne (riccatiOp u - riccatiOp v) ≤ L * normW Weight.constOne (u - v) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ContVersion
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ContVersion` -/
@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace SignatureVolatility

/-- Left dyadic approximant `⌊t 2ⁿ⌋₊ / 2ⁿ` of `t`. -/
def dyadicFloor (n : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n

variable {Ω : Type*}

/-- Continuous version of `X` read along left dyadic approximants. -/
def contVersion (X : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => X (dyadicFloor n t) ω

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.TimeReindex
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TimeReindex` -/
@[expose] public section

open MeasureTheory
open scoped NNReal

namespace SignatureVolatility

/-- Clamp a real time to nonnegative (`max t 0`). -/
noncomputable def toNNRealTime (t : ℝ) : ℝ≥0 := Real.toNNReal t

/-- Coordinatewise reindex for `Fin d`-valued drivers. -/
noncomputable def reindexProcessFin {Ω : Type*} {d : ℕ}
    (X : ℝ≥0 → Ω → Fin d → ℝ) : ℝ → Ω → Fin d → ℝ :=
  fun t ω i => X (toNNRealTime t) ω i

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.OfBrownian
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.OfBrownian` -/
@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace SignatureVolatility

/-- A `d`-dimensional Brownian driver on `ℝ≥0`, packaged for reindexing to the
signature-volatility `ℝ`-time API. Coordinates are one-dimensional Brownian
motions in the sense of Mathlib's `IsBrownianReal`, with **everywhere**-continuous
paths and coordinate **processes** that are mutually independent (so `W` is a
`d`-dimensional Brownian motion in its own joint filtration and joint-filtration
martingale calculi are available; a.s.-only continuity and coordinates that are
independent at each fixed time but entangled across times — e.g. one coordinate
anticipating the future of another — are excluded). -/
structure MultiBrownian (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Coordinate processes on Mathlib time `ℝ≥0`. -/
  Wnn : ℝ≥0 → Ω → Fin d → ℝ
  isBrownian : ∀ i : Fin d, IsBrownianReal (fun t ω => Wnn t ω i) P
  Wnn_zero : ∀ ω i, Wnn 0 ω i = 0
  Wnn_meas : ∀ t i, Measurable (fun ω => Wnn t ω i)
  /-- Paths are continuous at every `ω` (not merely almost every). -/
  pathContinuous : ∀ (i : Fin d) (ω : Ω), Continuous fun t : ℝ≥0 => Wnn t ω i
  /-- The coordinate **processes** `ω ↦ (t ↦ W_t^i(ω))` are mutually independent (path space
  `ℝ≥0 → ℝ` with the product σ-algebra). Strictly stronger than independence of the coordinates
  at each fixed time (`coordsIndep_eval`): it rules out future-entangled coordinates, for which
  an integrand `σ(t, W_t)` would anticipate the driver and Novikov / the Doléans SDE fail. -/
  coordsIndep : iIndepFun (fun i : Fin d => fun ω => fun t : ℝ≥0 => Wnn t ω i) P

namespace MultiBrownian

/-- Reindexed driver `ℝ → Ω → Fin d → ℝ` (negative times read time `0`). -/
def W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) : ℝ → Ω → Fin d → ℝ :=
  reindexProcessFin B.Wnn

lemma W_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (ω : Ω) (i : Fin d) : W B 0 ω i = 0 := by
  sorry
lemma W_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (i : Fin d) :
    Measurable (fun ω => W B t ω i) := by
  sorry
end MultiBrownian

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM` -/
@[expose] public section

open MeasureTheory Filter Topology
open scoped Interval NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Space increment of coordinate `i` between `ℝ`-times `s` and `t` via `toNNReal`. -/
def wnnIncr (B : MultiBrownian Ω P d) (i : Fin d) (s t : ℝ) (ω : Ω) : ℝ :=
  B.Wnn (Real.toNNReal t) ω i - B.Wnn (Real.toNNReal s) ω i

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ItoIntegralProcess
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ItoIntegralProcess` -/
@[expose] public section

open MeasureTheory Filter

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Dyadic left Riemann sum for `∫_s^t H_u du`. -/
def lebRiemann_process (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ k ∈ Finset.range (n + 1), H (s + (k : ℝ) * Δ) ω * Δ

/-- Pathwise Lebesgue `∫_s^t H_u du` as dyadic Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def lebIntegral_process (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => lebRiemann_process H s t n ω else 0

/-- Dyadic left Itô–Riemann sum for `∫_s^t H_u dW^k`. -/
def itoRiemann_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Δ := (t - s) / (n + 1 : ℕ)
  ∑ j ∈ Finset.range (n + 1),
    H (s + (j : ℝ) * Δ) ω *
      wnnIncr B k (s + (j : ℝ) * Δ) (s + ((j : ℝ) + 1) * Δ) ω

/-- Pathwise Itô `∫_s^t H_u dW^k` as dyadic Itô–Riemann `limUnder` (0 if `¬ s ≤ t`). -/
def itoIntegral_process (B : MultiBrownian Ω P d) (k : Fin d)
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if _h : s ≤ t then limUnder atTop fun n => itoRiemann_process B k H s t n ω else 0

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Space letter `j : Fin (d+1)` with `j ≠ 0` as a Brownian coordinate index. -/
def spaceLetterIndex (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0) : Fin d :=
  ⟨j.1 - 1, by
    have : j.1 < d + 1 := j.isLt
    omega⟩

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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralConsLong
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralConsLong` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Recursive Itô step for previous words of length `≥ 2`, given as process `H`. -/
def itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if hj : (j : ℕ) = 0 then lebIntegral_process H s t ω
  else itoIntegral_process B (spaceLetterIndex j hj) H s t ω

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Weighted contraction list of `I` (paper Appendix): every choice `Γ` of non-overlapping
adjacent equal space-letter pairs, each pair replaced by the time letter `0`, paired with its
weight `(1/2)^|Γ|`. Built by recursion on the first letter: either it is left alone, or (when
it is a space letter equal to the next one) the first pair is contracted. The head entry is the
empty contraction `(1, I)`. -/
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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Path filtration of `W` (same generators as `sig_adapted_to_W`). -/
def pathFiltration (B : MultiBrownian Ω P d) : IndexedFiltration Ω :=
  generatedFiltration (fun u i ω => MultiBrownian.W B u ω i) (MultiBrownian.W_meas B)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.MathFinBridge
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.MathFinBridge` -/
@[expose] public section

open MeasureTheory Filter
open scoped Classical

noncomputable section

namespace SignatureVolatility

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

/-- Quadratic variation: condExp onto the path filtration when the pair is integrable, else `0`. -/
def kitQuadVar (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    condExp ((pathFiltration B).σAlg t) P (kitQuadVarRaw B H t)
  else
    fun _ => 0

/-- Doléans exponential built from kit Itô / QV. -/
def kitDoleansExp (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (kitItoInt B σ t ω - (1 / 2 : ℝ) * kitQuadVar B σ t ω)

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.PaperSig
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.PaperSig` -/
@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Paper Stratonovich signature of the time-extended Brownian path (iterated integrals). -/
def paperSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I.reverse⟩

lemma paperSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [] = 1 := by
  sorry
lemma paperSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [0] = t - s := by
  sorry
lemma paperSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (paperSig2 B s t ω).coeff [i.succ] = MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  sorry
lemma measurable_paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (paperSig2 B s t ω).coeff I) := by
  sorry
lemma measurable_paperSig2_coeff_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => (paperSig2 B s t ω).coeff I) := by
  sorry
/-- **Paper Proposition 12 / Appendix A**: factorial level control of the Brownian signature
against weights of at most geometric growth. -/
theorem paperSig2_factorial_moment_control (B : MultiBrownian Ω P d) (p : ℝ) (hp : 1 ≤ p)
    (w_fn : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w_fn n) (hgeom : ∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, Summable (fun n : ℕ => w_fn n * (paperSig2 B 0 t ω).levelNorm n)) ∧
      Integrable (fun ω => (∑' n : ℕ, w_fn n * (paperSig2 B 0 t ω).levelNorm n) ^ p) P := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics` -/
@[expose] public section

noncomputable section


open MeasureTheory Filter Topology Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Signature dynamics** `dŴ = Ŵ ⊗ ∘dX` for the Brownian Stratonovich signature. -/
theorem paperSig2_dynamics (B : MultiBrownian Ω P d) (I : Word (d + 1)) (j : Fin (d + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [j])) := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.PaperSigChen
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.PaperSigChen` -/
@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Chen's identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_chen (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B 0 t ω = paperSig2 B 0 s ω ⊗ₜ paperSig2 B s t ω := by
  sorry
/-- **Shuffle identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_shuffle (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (I J : Word (d + 1)) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff I * (paperSig2 B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (paperSig2 B 0 t ω) := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM` -/
@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Paper goal.** `ProlongedBrownianSetup` whose `sig2` is the Stratonovich/Itô signature of
`(t, W_t)`, discharging Chen, shuffle, adaptedness, and Appendix A factorial moments. -/
noncomputable def prolongedBrownianSetup_stratonovich_of_brownian {T : ℝ}
    (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ProlongedBrownianSetup Ω P d T where
  hT_pos := hT
  W := MultiBrownian.W B
  W_zero := MultiBrownian.W_zero B
  W_meas := MultiBrownian.W_meas B
  sig2 := paperSig2 B
  sig_meas := measurable_paperSig2_coeff B
  sig2_empty := paperSig2_empty B
  sig2_time := paperSig2_time B
  sig2_space := paperSig2_space B
  sig_adapted_to_W := fun _t s I =>
    measurable_paperSig2_coeff_pathFiltration B le_rfl s.2.1 s.2.2 I
  stratonovich_chen := fun _s _t hs hst _ => paperSig2_chen B hs hst
  stratonovich_shuffle := fun _t ht0 _ I J => paperSig2_shuffle B ht0 I J
  stratonovich_dynamics := fun I j _t ht0 _ => paperSig2_dynamics B I j ht0
  factorial_moment_control := fun p hp w_fn hw0 hgeom _t ht0 _ =>
    paperSig2_factorial_moment_control B p hp w_fn hw0 hgeom ht0

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.DoleansSDE
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.DoleansSDE` -/
@[expose] public section

open MeasureTheory Filter Topology Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Doléans SDE for the signature volatility under H1–H3, pathwise square-integrability and
pathwise continuity of `σ`. Proved for `d = 0` and for constant `σ`; the non-constant case with a
driver is `kit_doleans_sde_of_driver`. -/
theorem kit_doleans_sde {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) (s₀ : ℝ) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    (∀ᵐ ω ∂P, ContinuousOn (fun s => σ s ω) (Icc 0 T)) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.StoppedL2
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.StoppedL2` -/
@[expose] public section

open MeasureTheory Set


namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Stopped L² localisation package under H1–H3, for **strong solutions**: adapted to the
signature filtration and in `KitStrongSolutionClass` (square-integrable supremum on `[0, T]` and
`L⁴`-regular integrand `S σ`).

Why these hypotheses (the paper's uniqueness is for strong solutions, i.e. continuous
semimartingales):
* without adaptedness the clause is false: `kitItoInt` zeroes non-measurable integrands
  (`forceMeasurable`), so on an incomplete space `s₀ + 𝟙_A` (`A` a non-measurable subset of a null
  set) is a spurious second solution;
* without H1–H2 the volatility need not have moments (e.g. `σ = exp(W⁴)`, `𝔼 ∫ σ² = ∞`), then
  `kitItoInt (s₀ σ) = 0` and the constant `s₀` solves the kit equation although it is not the
  paper's price;
* without the regularity class an adapted process is not a semimartingale solution: the kit's
  integral at `t` only samples the integrand at `q t`, `q ∈ ℚ`, and is linear / isometric only on
  regular integrands. The constructed Doléans price is in the class
  (`kit_doleans_strong_class`). -/
theorem kit_stopped_l2_localisation {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (_hℓ : HypH1 w ℓ) (s₀ : ℝ)
    (S₁ S₂ : ℝ → Ω → ℝ) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₁ t)) →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₂ t)) →
    KitStrongSolutionClass P T σ S₁ →
    KitStrongSolutionClass P T σ S₂ →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₁ t ω = s₀ + kitItoInt B (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₂ t ω = s₀ + kitItoInt B (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    ∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) →
        ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P, S₁ t ω = S₂ t ω) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.NovikovDoob
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.NovikovDoob` -/
@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Novikov–Doob L² martingale package under H1–H3. -/
theorem kit_novikov_doob_l2_martingale {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * kitDoleansExp B σ t ω
    HypH3 P T σ →
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) P ∧
      P[S t | setup.signatureFiltration.σAlg s] =ᵐ[P] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) P) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.ItoQuadDoleans
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.ItoQuadDoleans` -/
@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Paper-setup Itô integral. -/
abbrev paperItoInt {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun H t ω => kitItoInt B H t ω

/-- Paper-setup quadratic variation. -/
abbrev paperQuadVar {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun H t ω => kitQuadVar B H t ω

/-- Paper-setup Doléans exponential. -/
abbrev paperDoleansExp {T : ℝ} (B : MultiBrownian Ω P d) (_hT : 0 < T) :
    (ℝ → Ω → ℝ) → ℝ → Ω → ℝ :=
  fun σ t ω => kitDoleansExp B σ t ω

lemma paperItoInt_zero {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (ω : Ω) :
    paperItoInt B hT H 0 ω = 0 := by
  sorry
lemma paperItoInt_meas {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (paperItoInt B hT H t) := by
  sorry
lemma paperItoInt_adapted {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (paperItoInt B hT H s.1) := by
  sorry
lemma paperQuadVar_zero {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (ω : Ω) :
    paperQuadVar B hT H 0 ω = 0 := by
  sorry
lemma paperQuadVar_meas {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (paperQuadVar B hT H t) := by
  sorry
lemma paperQuadVar_adapted {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(prolongedBrownianSetup_stratonovich_of_brownian B hT).signatureFiltration.σAlg t]
      (paperQuadVar B hT H s.1) := by
  sorry
lemma paperDoleansExp_def {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    paperDoleansExp B hT σ t ω =
      Real.exp (paperItoInt B hT σ t ω - (1 / 2 : ℝ) * paperQuadVar B hT σ t ω) := by
  sorry
end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.DoleansStrongClass
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.DoleansStrongClass` -/
@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **The constructed Doléans solution is in the strong-solution class.** -/
theorem kit_doleans_strong_class {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) (s₀ : ℝ)
    (hs₀ : 0 < s₀) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    KitStrongSolutionClass P T σ (fun t ω => s₀ * paperDoleansExp B hT σ t ω) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.ItoCalculusKit.OfMathFin
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.ItoCalculusKit.OfMathFin` -/
@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Abbreviation: paper-strength prolonged setup from a multi-Brownian driver. -/
noncomputable abbrev paperSetup {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :=
  prolongedBrownianSetup_stratonovich_of_brownian B hT

/-- **Paper goal.** `ItoCalculusKit` over the Stratonovich prolonged setup. -/
noncomputable def itoCalculusKit_of_mathfin {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ItoCalculusKit Ω P d T (paperSetup B hT) where
  itoInt := paperItoInt B hT
  itoInt_zero := paperItoInt_zero B hT
  itoInt_meas := paperItoInt_meas B hT
  itoInt_adapted := paperItoInt_adapted B hT
  quadVar := paperQuadVar B hT
  quadVar_zero := paperQuadVar_zero B hT
  quadVar_meas := paperQuadVar_meas B hT
  quadVar_adapted := paperQuadVar_adapted B hT
  doleansExp := paperDoleansExp B hT
  doleansExp_def := paperDoleansExp_def B hT
  doleans_sde := kit_doleans_sde B hT
  stopped_l2_localisation := kit_stopped_l2_localisation B hT
  novikov_doob_l2_martingale := kit_novikov_doob_l2_martingale B hT
  doleans_strong_class := kit_doleans_strong_class B hT

end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.SignaturePriceSolution
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignaturePriceSolution` -/
@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

structure SignaturePriceSolution {Ω : Type*} [MeasurableSpace Ω]
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
    (∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 M.T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ
  is_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
    Integrable (S t) ℙ ∧
    ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.TheoremA
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremA` -/
@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem A.** Existence/uniqueness of the signature-price solution over Brownian motion
(Stratonovich prolonged setup + MathFin Ito kit). Uniqueness is among strong solutions: adapted to
the signature filtration and in `KitStrongSolutionClass` (square-integrable supremum, `L⁴`-regular
integrand), which the constructed Doléans solution satisfies. -/
theorem theorem_A (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT),
      ∀ S_tilde : ℝ → Ω → ℝ,
        (∀ t ∈ Icc 0 M.T, Measurable[(paperSetup B M.hT).signatureFiltration.σAlg t] (S_tilde t)) →
        KitStrongSolutionClass P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))
          S_tilde →
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P,
          S_tilde t ω = M.s₀ + (itoCalculusKit_of_mathfin B M.hT).itoInt
            (fun s ω' => S_tilde s ω' *
              SignatureVolatilityModel.sigma M (paperSetup B M.hT) s ω')
            t ω) →
        ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂P, S_tilde t ω = sol.S t ω := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.PriceFiltrationSignatureSpace.OfMarket
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.PriceFiltrationSignatureSpace.OfMarket` -/
@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

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

/-- `L²(ℱ^S_T, ℚ)` (with `ℚ = ℙ`) as a closed subspace of `L²(ℙ)`. -/
abbrev L2S (mkt : MarketData Ω P) : Submodule ℝ (Lp ℝ 2 P) :=
  lpMeas ℝ ℝ mkt.F_ST 2 P

lemma memLp_coord (mkt : MarketData Ω P) (I : Word (mkt.M.d + 1)) :
    MemLp (fun ω => (mkt.setup.W_hat mkt.M.T ω).coeff I) 2 P := by
  sorry
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

end MarketData

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.Prop58BlackScholesDepthFalse
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.Prop58BlackScholesDepthFalse` -/
@[expose] public section


open MeasureTheory ProbabilityTheory Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)

/-- The Black–Scholes volatility is the constant `σ₀`. -/
lemma sigma_blackScholes (B : MultiBrownian Ω P 1) :
    SignatureVolatilityModel.sigma (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀) (paperSetup B hT) =
      fun _ _ => σ₀ := by
  sorry
/-- The Black–Scholes market on a one-dimensional Brownian driver. Here H3 holds trivially,
because the volatility is constant. -/
def blackScholesMarket (B : MultiBrownian Ω P 1) : MarketData Ω P where
  M := blackScholesModel T s₀ σ₀ hT hs₀ hσ₀
  B := B
  h3 := by
    change HypH3 P T (SignatureVolatilityModel.sigma (blackScholesModel T s₀ σ₀ hT hs₀ hσ₀)
      (paperSetup B hT))
    rw [sigma_blackScholes]
    intro _ _
    exact integrable_const _

/-- **Black–Scholes has infinite completeness depth** under the paper's Definition 55. -/
theorem blackScholes_completenessDepth_eq_top (B : MultiBrownian Ω P 1) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth = ⊤ := by
  sorry
/-- **Counterexample to Proposition 58 (PDF Prop. 5.5).** Black–Scholes does *not* have
`N^*_S = 0`. -/
theorem not_prop58_blackScholes_depth_zero (B : MultiBrownian Ω P 1) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth ≠ 0 := by
  sorry
end SignatureVolatility
end

end

section
-- source module: BrownianMotion.StochasticIntegral.SimpleProcess
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `BrownianMotion.StochasticIntegral.SimpleProcess` -/
@[expose] public section

open MeasureTheory Finset Filter ContinuousLinearMap
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [mE : MeasurableSpace E]
variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓕 : Filtration ι mΩ}

/-- A **simple process** is defined as a finite sum of indicator functions of intervals `(s, t]`,
each assigned to a bounded `𝓕 s`-measurable random variable `value`, plus a `valueBot` at ⊥. -/
@[ext]
structure SimpleProcess (F : Type*) [NormedAddCommGroup F] [MeasurableSpace F] [NormedSpace ℝ F]
    [BorelSpace F] [SecondCountableTopology F] (𝓕 : Filtration ι mΩ) where
  /-- The value at ⊥. -/
  valueBot : Ω → F
  /-- The value on each interval. Note that intervals are not necessarily disjoint. -/
  value : ι × ι →₀ Ω → F
  /-- The intervals in the support of `value` are ordered. -/
  le_of_mem_support_value : ∀ p ∈ value.support, p.1 ≤ p.2
  /-- The value at ⊥ is measurable with respect to the filtration at ⊥. -/
  measurable_valueBot : Measurable[𝓕 ⊥] valueBot := by
    first | measurability | eta_expand; measurability
  /-- The value on each interval is measurable with respect to the filtration at the left endpoint.

  Do not use this lemma directly. Use `SimpleProcess.measurable_value` instead. -/
  measurable_value' : ∀ p ∈ value.support, Measurable[𝓕 p.1] (value p) := by
    -- Note: Most of the time we need to eta-expand to make `fun_prop` find the right lemma,
    -- such as `Measurability.neg` that can only recognize `fun x ↦ -f x` rather than `-f`.
    -- On the other hand, some other lemmas like `Measurable.const_smul` can only recognize `c • f`
    -- rather than `fun x ↦ c • f x`, so we also need to try directly applying `measurability`.
    first | measurability | eta_expand; measurability
  /-- The value at ⊥ is bounded. -/
  bounded_valueBot : ∃ C : ℝ, ∀ ω : Ω, ‖valueBot ω‖ ≤ C
  /-- The value on each interval is bounded. -/
  bounded_value : ∃ C : ℝ, ∀ p ∈ value.support, ∀ ω : Ω, ‖value p ω‖ ≤ C

namespace SimpleProcess

attribute [fun_prop] measurable_valueBot

/-- A bound on the value at ⊥. -/
noncomputable def valueBotBound (V : SimpleProcess E 𝓕) : ℝ := max 0 V.bounded_valueBot.choose

/-- The value at ⊥ is bounded by `valueBotBound`. -/
@[simp] lemma valueBot_le_valueBotBound (V : SimpleProcess E 𝓕) (ω : Ω) :
    ‖V.valueBot ω‖ ≤ V.valueBotBound := by
  sorry
/-- The value of the simple process at the left endpoint of an interval is measurable
with respect to the filtration at the left endpoint.

Note that we do not require `p ∈ V.value.support`, because the value is 0 otherwise,
which is measurable. -/
@[fun_prop]
lemma measurable_value (V : SimpleProcess E 𝓕) (p : ι × ι) : Measurable[𝓕 p.1] (V.value p) := by
  sorry
/-- A nonnegative bound on the value on each interval. -/
noncomputable def valueBound (V : SimpleProcess E 𝓕) : ℝ := max 0 (V.bounded_value.choose)

/-- The value on each interval is bounded by `valueBound`. Note that we do not require
`p ∈ V.value.support`. -/
@[simp] lemma value_le_valueBound (V : SimpleProcess E 𝓕) (p : ι × ι) (ω : Ω) :
    ‖V.value p ω‖ ≤ V.valueBound := by
  sorry
section Module

@[simps]
instance instZero : Zero (SimpleProcess E 𝓕) where
  zero := {
    valueBot := 0,
    value := 0,
    le_of_mem_support_value := by simp,
    bounded_valueBot := ⟨0, by simp⟩,
    bounded_value := ⟨0, by simp⟩ }

@[simps]
instance instNeg : Neg (SimpleProcess E 𝓕) where
  neg V := {
    valueBot := -V.valueBot,
    value := -V.value,
    le_of_mem_support_value := by simpa using V.le_of_mem_support_value,
    bounded_valueBot := ⟨V.valueBotBound, by simp⟩,
    bounded_value := ⟨V.valueBound, by simp⟩ }

@[simps]
instance instAdd : Add (SimpleProcess E 𝓕) where
  add V W := {
    valueBot := V.valueBot + W.valueBot,
    value := V.value + W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_add hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    measurable_value' p hp := by
      simp only [Finsupp.coe_add, Pi.add_apply]
      exact Measurable.add (by fun_prop) (by fun_prop)
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_add_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_add_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSub : Sub (SimpleProcess E 𝓕) where
  sub V W := {
    valueBot := V.valueBot - W.valueBot,
    value := V.value - W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_sub hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    measurable_value' p hp := by
      simp only [Finsupp.coe_sub, Pi.sub_apply]
      exact Measurable.sub (by fun_prop) (by fun_prop)
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_sub_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_sub_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }

@[simps]
instance instSMul : SMul ℝ (SimpleProcess E 𝓕) where
  smul c V := {
    valueBot := c • V.valueBot,
    value := c • V.value,
    le_of_mem_support_value := by simpa using fun p _ ↦ V.le_of_mem_support_value p,
    bounded_valueBot := ⟨|c| * V.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_smul, V.valueBot_le_valueBotBound, Real.norm_eq_abs]⟩,
    bounded_value := ⟨|c| * V.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_smul, V.value_le_valueBound, Real.norm_eq_abs]⟩ }

instance instAddCommGroup : AddCommGroup (SimpleProcess E 𝓕) where
  sub_eq_add_neg U V := by ext <;> apply sub_eq_add_neg
  add_assoc U V W := by ext <;> apply add_assoc
  add_comm U V := by ext <;> apply add_comm
  zero_add V := by ext <;> apply zero_add
  add_zero V := by ext <;> apply add_zero
  neg_add_cancel V := by ext <;> apply neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SimpleProcess E 𝓕) where
  zero_smul V := by ext <;> simp
  smul_zero V := by ext <;> simp
  add_smul U V W := by ext <;> simp [add_smul]
  smul_add U V W := by ext <;> simp [smul_add]
  one_smul V := by ext <;> simp
  mul_smul U V W := by ext <;> simp [mul_smul]

end Module

section ToFun

/-- Coercion from a simple process to a function. Note that this is not injective. -/
@[coe] def toFun (V : SimpleProcess E 𝓕) (i : ι) (ω : Ω) : E :=
  ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i

instance instCoeFun : CoeFun (SimpleProcess E 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := toFun

end ToFun

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

end SimpleProcess

end ProbabilityTheory
end
end

end

section
-- source module: BrownianMotion.StochasticIntegral.Predictable
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `BrownianMotion.StochasticIntegral.Predictable` -/
@[expose] public section

open Filter Function MeasureTheory Order Set TopologicalSpace

open scoped NNReal ENNReal Topology

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {E : Type*} [TopologicalSpace E] [PartialOrder ι]

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] [OrderBot ι]

/-- The predictable σ-algebra is a sub-σ-algebra of the product σ-algebra. -/
lemma predictable_le_prod {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    [OrderTopology T] [MeasurableSpace T] [BorelSpace T] (𝓕 : Filtration T m) :
    𝓕.predictable ≤ Prod.instMeasurableSpace := by
  sorry
end MeasureTheory.Filtration
end

end

section
-- source module: MathFin.Probability.Brownian.Ito.ItoIntegralL2
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `MathFin.Probability.Brownian.Ito.ItoIntegralL2` -/
@[expose] public section

namespace MathFin
namespace ItoIntegralL2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The **natural Brownian filtration** `𝓕ᴮ_t = σ(B_u : u ≤ t)`. -/
noncomputable def natFiltration (hBmeas : ∀ t, Measurable (B t)) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t ↦ (hBmeas t).stronglyMeasurable)

/-- The **elementary Itô integral** of a simple process `V` against Brownian motion
`B`, evaluated at the terminal time: `(V ● B)_⊤ = ∑ₚ V(p)·(B_{p.2} − B_{p.1})`,
the increment sum with nothing truncated.

Until the 2026-07-27 pin this *was* Degenne's `SimpleProcess.integral … ⊤`: his
elementary integral was indexed by `WithTop ι`, so `⊤` named the untruncated
value and `SimpleProcess.integral_top` unfolded it to this sum. At the new pin
`integral : ι → Ω → G` — the index dropped `WithTop`, `integral_top` is
commented out upstream, and with `ι = ℝ≥0` there is no `⊤` to evaluate at. The
untruncated value is therefore no longer *expressible* as an evaluation of
`integral`, and is taken as the definition here.

Nothing downstream is weakened: every consumer goes through `itoSimple_apply`
(now definitional), and the process-level integral `itoSimpleProcess` still
consumes `SimpleProcess.integral` directly, at a genuine time `t : ℝ≥0`.
Restoring the consumption relation — `itoSimple = integral … t` for any `t`
dominating `V`'s finite support — is a follow-up recorded in
`docs/archive/upstream-consumption-review-2026-07-27.md`. -/
noncomputable def itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Ω → ℝ :=
  fun ω ↦ V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω)

variable [IsProbabilityMeasure μ]

/-- **Step 1 — `L²` membership.** The terminal Itô integral of a simple process is in
`L²(μ)`: it is the finite sum `∑ₚ V(p)·(B_{p.2}−B_{p.1})`, and each summand is in `L²`
by `memLp_adapted_mul_increment` — the coefficient `V(p)` is `𝓕_{p.1}`-measurable (the
filtration the core is stated against) and bounded (hence `L²` on the probability space). -/
theorem memLp_itoSimple (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (itoSimple hBmeas V) 2 μ := by
  sorry
/-- The terminal Itô integral of a simple process as an element of `Lp ℝ 2 μ`. -/
noncomputable def itoSimpleLp (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Lp ℝ 2 μ :=
  (memLp_itoSimple hB hBmeas V).toLp _

/-- Lebesgue measure on the time axis `ℝ≥0` — the comap of `volume` along `ℝ≥0 ↪ ℝ`. -/
noncomputable def timeMeasure : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- The uncurried simple process is `L²` in the **trimmed** (predictable) product
measure: it is predictable-strongly-measurable (`SimpleProcess.isStronglyPredictable`)
with the same finite `L²` norm as in the untrimmed product (`eLpNorm_trim`). -/
lemma memLp_uncurry_trim (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2
      ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) := by
  sorry
/-- **The embedding** of a simple process into the predictable `L²` space, as the class of
its uncurried version. The codomain `Lp ℝ 2 ((timeMeasure.prod μ).trim …)` is *definitionally*
Degenne's `L2Predictable timeMeasure μ`; we keep it unfolded here so the `Lp` norm instance is
available (the opaque `L2Predictable` def has none), and re-wrap as `L2Predictable` only at the
final continuous integral. The Itô isometry identifies its norm with that of `itoSimpleLp`. -/
noncomputable def simpleProcessL2 (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) :=
  (memLp_uncurry_trim hBmeas V).toLp (Function.uncurry ⇑V)

/-- The elementary Itô integral is additive in the simple process. -/
lemma itoSimple_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimple hBmeas (V + W) = itoSimple hBmeas V + itoSimple hBmeas W := by
  sorry
/-- The elementary Itô integral is homogeneous in the simple process. -/
lemma itoSimple_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimple hBmeas (c • V) = c • itoSimple hBmeas V := by
  sorry
/-- **The elementary Itô integral as a linear map** `SimpleProcess →ₗ[ℝ] Lp ℝ 2 μ`. -/
noncomputable def itoAssembly (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleLp hB hBmeas V
  map_add' V W := by
    rw [itoSimpleLp, itoSimpleLp, itoSimpleLp,
        ← MemLp.toLp_add (memLp_itoSimple hB hBmeas V) (memLp_itoSimple hB hBmeas W)]
    congr 1
    exact itoSimple_add hBmeas V W
  map_smul' c V := by
    rw [itoSimpleLp, itoSimpleLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimple hB hBmeas V)]
    congr 1
    exact itoSimple_smul hBmeas c V

/-- The uncurried simple process is additive. -/
lemma uncurry_coe_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑(V + W) = Function.uncurry ⇑V + Function.uncurry ⇑W := by
  sorry
/-- The uncurried simple process is homogeneous. -/
lemma uncurry_coe_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑(c • V) = c • Function.uncurry ⇑V := by
  sorry
/-- **The embedding into the predictable `L²` as a linear map**
`SimpleProcess →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim …)`. -/
noncomputable def simpleAssembly (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)
      →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) where
  toFun V := simpleProcessL2 (μ := μ) hBmeas V
  map_add' V W := by
    rw [simpleProcessL2, simpleProcessL2, simpleProcessL2,
        ← MemLp.toLp_add (memLp_uncurry_trim hBmeas V) (memLp_uncurry_trim hBmeas W)]
    congr 1
    exact uncurry_coe_add hBmeas V W
  map_smul' c V := by
    rw [simpleProcessL2, simpleProcessL2, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim hBmeas V)]
    congr 1
    exact uncurry_coe_smul hBmeas c V

end ItoIntegralL2
end MathFin
end

end

section
-- source module: MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense` -/
@[expose] public section

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralCLM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- The restriction of `timeMeasure` (the σ-finite Lebesgue pushforward to
`ℝ≥0`, defined in `ItoIntegralL2.lean`) to `Ioc 0 T`. Finite of total mass `T`. -/
noncomputable def timeMeasureHorizon (T : ℝ≥0) : Measure ℝ≥0 :=
  ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)

/-- The product measure `timeMeasureHorizon T ⊗ μ`, trimmed to the predictable
σ-algebra of the natural Brownian filtration. The `L²`-domain of the CLM.

Reuses Degenne's `Filtration.predictable_le_prod` (upstream `L2M.lean` L27),
which is exactly the σ-algebra hypothesis `extendOfNorm` consumes.

The return type is left implicit so the σ-algebra is the predictable one (the
`trim` result), not the default `Prod.instMeasurableSpace` — annotating the
return type would force the default and cause an `Application type mismatch`. -/
noncomputable def trimMeasure (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :=
  ((timeMeasureHorizon T).prod μ).trim
    (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod

/-- **Bridge.** The T-restricted predictable trim equals the restriction of the
full predictable trim to `Ioc 0 T × univ`. Proof: `prod_restrict_eq_prod_univ`
moves the time-restrict out of the product, then `restrict_trim` swaps `restrict`
and `trim` (legal because `Ioc 0 T × univ` is a basic predictable rectangle, hence
predictable-measurable). -/
lemma trimMeasure_eq_restrict (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    trimMeasure (μ := μ) T hBmeas =
      ((ItoIntegralL2.timeMeasure.prod μ).trim
        (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict
        (Set.Ioc 0 T ×ˢ Set.univ) := by
  sorry
variable (hB : IsPreBrownianReal B μ)

end ItoIntegralCLM
end MathFin
end

end

section
-- source module: MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `MathFin.Probability.Brownian.Ito.ItoIntegralL2Dense` -/
@[expose] public section

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) [IsProbabilityMeasure μ]

include hB

/-- **The unbounded-horizon Itô integral as a CLM.** Built from `itoAssembly`
along the (now dense) `simpleAssembly` via `LinearMap.extendOfNorm`. Its domain
`Lp ℝ 2 trim_full` is Degenne's `L2Predictable timeMeasure μ`. -/
noncomputable def itoIntegralL2 (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) →L[ℝ] Lp ℝ 2 μ :=
  (itoAssembly (μ := μ) hB hBmeas).extendOfNorm (simpleAssembly (μ := μ) hBmeas)

end ItoIntegralL2
end MathFin
end

end

section
-- source module: MathFin.Probability.Brownian.Ito.ItoIntegralCLM
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `MathFin.Probability.Brownian.Ito.ItoIntegralCLM` -/
@[expose] public section

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralCLM

open ItoIntegralL2

section MonoMeasureLp
variable {α : Type*} {_mα : MeasurableSpace α} {μ ν : Measure α}

/-- **The `Lp` inclusion for `ν ≤ μ`.** For `f ∈ Lp 2 μ` the *same* function lies in
`Lp 2 ν` with no larger norm (a smaller measure can only shrink the `L²` norm), so
`f ↦ f` is a norm-`≤ 1` continuous linear map `Lp 2 μ →L[ℝ] Lp 2 ν`. Mathlib has
`MemLp.mono_measure` but no packaged CLM; generic measure theory, a natural upstream
candidate. Specialises to measure restriction (`ν = μ.restrict s`, via
`Measure.restrict_le_self`). -/
noncomputable def monoMeasureLp (h : ν ≤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure h).toLp
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure h),
          Lp.coeFn_add (((Lp.memLp f).mono_measure h).toLp) (((Lp.memLp g).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure h),
          (Lp.coeFn_add f g).filter_mono (ae_mono h)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure h),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          (Lp.coeFn_smul c f).filter_mono (ae_mono h)] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply] }
    1 (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top ?_
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h))]
      exact eLpNorm_mono_measure _ h)

end MonoMeasureLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **Restriction of a `[0,∞)` predictable integrand to the band `[0,T]`** as a CLM
`Lp 2 trim_full →L[ℝ] Lp 2 (trimMeasure T)`: the `Lp` inclusion for
`trimMeasure T ≤ trim_full` (the band restriction, `trimMeasure_eq_restrict` +
`Measure.restrict_le_self`). The integrand seen on `[0,T]`. -/
noncomputable def restrictToBand (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)
      →L[ℝ] Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  monoMeasureLp ((trimMeasure_eq_restrict T hBmeas).le.trans Measure.restrict_le_self)

/-- Restricting to the band `(0,T] × Ω` commutes with taking indicators: a.e.-equality in
the `[0,T]` trim lifts to a.e.-equality of the band indicators in the `[0,∞)` trim. -/
lemma indicator_band_ae_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {f g : ℝ≥0 × Ω → ℝ} (h : f =ᵐ[trimMeasure (μ := μ) T hBmeas] g) :
    (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator f
      =ᵐ[(timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod]
        (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator g := by
  sorry
lemma memLp_indicator_band (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator φ) 2
      ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) := by
  sorry
/-- **Extension by zero** of a `[0,T]` integrand to the `[0,∞)` predictable `L²`: the
isometric section of `restrictToBand`. -/
noncomputable def bandExtend (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →ₗᵢ[ℝ]
      Lp ℝ 2 ((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) where
  toFun φ := (memLp_indicator_band T hBmeas φ).toLp
    ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator φ)
  map_add' φ ψ := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_band T hBmeas (φ + ψ)),
      Lp.coeFn_add ((memLp_indicator_band T hBmeas φ).toLp _)
        ((memLp_indicator_band T hBmeas ψ).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas φ),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas ψ),
      indicator_band_ae_eq T hBmeas (Lp.coeFn_add φ ψ)] with z h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, Set.indicator_add']
  map_smul' c φ := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_band T hBmeas (c • φ)),
      Lp.coeFn_smul c ((memLp_indicator_band T hBmeas φ).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_band T hBmeas φ),
      indicator_band_ae_eq T hBmeas (Lp.coeFn_smul c φ)] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply]
    by_cases hz : z ∈ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.smul_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, smul_zero]
  norm_map' φ := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def,
        eLpNorm_indicator_eq_eLpNorm_restrict
      (MeasureTheory.measurableSet_predictable_Ioc_prod
        (𝓕 := natFiltration (mΩ := mΩ) hBmeas) 0 T MeasurableSet.univ).nullMeasurableSet,
      ← trimMeasure_eq_restrict]

/-- **The Itô integral on `[0,T]`**: the infinite-horizon integral `itoIntegralL2` of the
integrand extended by zero (`bandExtend`). A continuous linear map as a composite of one. -/
noncomputable def itoIntegralCLM (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoIntegralL2 hB hBmeas).comp (bandExtend T hBmeas).toContinuousLinearMap

end ItoIntegralCLM
end MathFin
end

end

section
-- source module: SignatureVolatility.TheoremCCounterExample
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremCCounterExample` -/
@[expose] public section

open MeasureTheory ProbabilityTheory
open MathFin MathFin.ItoIntegralCLM MathFin.ItoIntegralL2
open scoped NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)

/-- The Brownian driver of the one-dimensional market. -/
def bsDriver (B : MultiBrownian Ω P 1) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B.Wnn t ω (kitDriver Nat.one_pos)

lemma bsDriver_meas (B : MultiBrownian Ω P 1) : ∀ t, Measurable (bsDriver B t) := by
  sorry
lemma bsDriver_isPreBrownian (B : MultiBrownian Ω P 1) : IsPreBrownianReal (bsDriver B) P := by
  sorry
/-- **Completeness with finitely many calls** (paper Theorem 56 / C, left-hand side), for the
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
  sorry
/-- **CounterExample_TheoremC.** For the Black–Scholes market and any finite set of call strikes,
the paper's equivalence "complete on `ℱ^S_T` ⇔ `N^*_S < ∞`" is false: the market is complete
but `N^*_S = ∞`. -/
theorem not_theorem_C (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    ¬ (IsCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes ↔
      (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.SatisfiesNFLVR
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SatisfiesNFLVR` -/
@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.SignatureRiccatiKit
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignatureRiccatiKit` -/
@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Transform finiteness** (paper Theorem 44(2) hypothesis), for one initial datum `u₀`: the
signature transform `𝔼 exp⟨u₀, Ŵ_t⟩` is finite on `[0, T]`. The paper quantifies this over *all*
`u₀ ∈ 𝒟_fin`; that global version fails for Brownian signatures (`u₀ = c e_{11}` gives
`𝔼 exp(c W_t² / 2) = ∞` once `c t ≥ 1`), so it is imposed per initial datum. -/
def SignatureTransformFinite {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) {d : ℕ} {T : ℝ}
    [IsProbabilityMeasure ℙ] (setup : ProlongedBrownianSetup Ω ℙ d T) (u₀ : ExtTensorAlgebra (d + 1)) :
    Prop :=
  ∀ t ∈ Icc 0 T, Integrable (fun ω => Real.exp (dualPairing u₀ (setup.W_hat t ω))) ℙ

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.SignatureRiccatiKit.AffineRiccatiDualityMp` -/
@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Affine / Riccati duality, `→` direction** (paper Theorem 4.2(ii), p. 21). If the
conditional signature transform of `u₀` is exponential-affine through a classical solution of the
Riccati equation `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, then a global classical Riccati solution exists. -/
theorem affine_riccati_duality_mp (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)) :
    SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
    (∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω))) P ∧
        P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) ((paperSetup B M.hT).W_hat t ω))) →
    Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.TheoremB
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremB` -/
@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem B, proved part** (no dependence on the open `affine_riccati_duality`): the
Theorem A price is a martingale on the signature filtration, NFLVR holds, and every signature
coordinate is a special semimartingale (Lemma 43). The full `theorem_B`, whose Riccati clause
rests on the open `affine_riccati_duality_mpr`, is in the non-submitted `OpenProblems` library
(`OpenProblems/TheoremB.lean`). -/
theorem theorem_B_proved (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (h3 : HypH3 P M.T (SignatureVolatilityModel.sigma M (paperSetup B M.hT))) :
    ∃ (sol : SignaturePriceSolution M (paperSetup B M.hT) (itoCalculusKit_of_mathfin B M.hT)),
      (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
        Integrable (sol.S t) P ∧
        P[sol.S t | (paperSetup B M.hT).signatureFiltration.σAlg s] =ᵐ[P] sol.S s) ∧
      SatisfiesNFLVR P (AdmissibleGainsUnderP P) ∧
      (∀ I : Word (M.d + 1),
        Nonempty (IsSpecialSemimartingale P
          (paperSetup B M.hT).signatureFiltration M.T
          (fun t ω => ((paperSetup B M.hT).W_hat t ω).coeff I))) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.TheoremC
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremC` -/
@[expose] public section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Theorem C, right-hand side, in every non-degenerate market.** If `L²(ℱ^S_T, ℚ)` is
infinite-dimensional, then the Definition 55 depth is `∞`, and no finite-depth closed signature
span restricted to the price filtration is dense in `L²(ℱ^S_T, ℚ)`. -/
theorem theorem_C_depth_infinite (mkt : MarketData Ω P)
    (hinf : ¬ FiniteDimensional ℝ mkt.L2S) :
    mkt.completenessDepth = ⊤ ∧
      ∀ N : ℕ, (mkt.sigSpan N).topologicalClosure ≠ mkt.L2S := by
  sorry
/-- **Theorem C, right-hand side, for Black–Scholes.** It fails at every finite depth. -/
theorem theorem_C_blackScholes_depth_infinite (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀)
    (hσ₀ : σ₀ ≠ 0) (B : MultiBrownian Ω P 1) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth = ⊤ ∧
      ∀ N : ℕ, ((blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).sigSpan N).topologicalClosure ≠
        (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).L2S := by
  sorry
/-- **CounterExample_TheoremC.** The paper's Theorem C ("complete with finitely many calls ⇔
`N^*_S < ∞`") fails for Black–Scholes, for every finite set of strikes. -/
theorem theorem_C_refuted (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)
    (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    ¬ (IsCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes ↔
      (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤) := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.GKWDecompositionSetup.OfPFS
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.GKWDecompositionSetup.OfPFS` -/
@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace MarketData

/-- The constant payoff `1 ∈ L²(ℙ)`. -/
def oneLp (P : Measure Ω) [IsProbabilityMeasure P] : Lp ℝ 2 P :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)

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

end MarketData

end SignatureVolatility
end
end

end

section
-- source module: SignatureVolatility.TheoremD
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremD` -/
@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Paper Theorem D / Theorem 66 (GKW part).** -/
theorem theorem_D (mkt : MarketData Ω P) (X : Lp ℝ 2 P) (hX : X ∈ mkt.L2S) :
    ∃ G ε : Lp ℝ 2 P,
      G ∈ mkt.H0 ∧ ⟪G, MarketData.oneLp P⟫ = 0 ∧ ε ∈ mkt.L2S ∧ ε ∈ mkt.H0ᗮ ∧
      (∀ Z ∈ mkt.gainsSet, ⟪ε, Z⟫ = 0) ∧
      X = (∫ ω, X ω ∂P) • MarketData.oneLp P + G + ε ∧
      ‖X‖ ^ 2 = ‖(∫ ω, X ω ∂P) • MarketData.oneLp P + G‖ ^ 2 + ‖ε‖ ^ 2 ∧
      ∀ (c : ℝ) (G' ε' : Lp ℝ 2 P), G' ∈ mkt.H0 → ⟪G', MarketData.oneLp P⟫ = 0 →
        ε' ∈ mkt.H0ᗮ → X = c • MarketData.oneLp P + G' + ε' →
          c = ∫ ω, X ω ∂P ∧ G' = G ∧ ε' = ε := by
  sorry
end SignatureVolatility
end

end

section
-- source module: SignatureVolatility.TheoremDCounterExample
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-! ## from `SignatureVolatility.TheoremDCounterExample` -/
@[expose] public section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P]

/-- The residual-expansion hypothesis `N^*_S < ∞` of Theorem 66 fails for Black–Scholes. -/
theorem theorem_D_residual_hypothesis_fails (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀)
    (hσ₀ : σ₀ ≠ 0) (B : MultiBrownian Ω P 1) :
    ¬ (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤ := by
  sorry
end SignatureVolatility
end

end
