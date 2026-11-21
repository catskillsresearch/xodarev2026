/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

/-- Finite ordered endpoints of `[0,T]`. Repetition permits degenerate horizons. -/
structure TimePartition (T : ℝ≥0) where
  size : ℕ
  point : Fin (size + 1) → ℝ≥0
  monotone_point : Monotone point
  first_eq_zero : point 0 = 0
  last_eq_horizon : point (Fin.last size) = T

namespace TimePartition

variable {T : ℝ≥0}

def left (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := π.point i.castSucc
def right (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := π.point i.succ

theorem left_le_right (π : TimePartition T) (i : Fin π.size) : π.left i ≤ π.right i :=
  π.monotone_point (by simp [Fin.le_def])

theorem point_le_horizon (π : TimePartition T) (i : Fin (π.size + 1)) : π.point i ≤ T := by
  exact (π.monotone_point (Fin.le_last i)).trans_eq π.last_eq_horizon

/-- Cell length; the ordering theorem justifies the nonnegative subtraction. -/
def gap (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := π.right i - π.left i

theorem gap_add_left (π : TimePartition T) (i : Fin π.size) :
    π.gap i + π.left i = π.right i := tsub_add_cancel_of_le (π.left_le_right i)

def mesh (π : TimePartition T) : ℝ≥0 := Finset.univ.sup π.gap

theorem gap_le_mesh (π : TimePartition T) (i : Fin π.size) : π.gap i ≤ π.mesh :=
  Finset.le_sup (f := π.gap) (Finset.mem_univ i)

def empty : TimePartition 0 where
  size := 0
  point := fun _ ↦ 0
  monotone_point := monotone_const
  first_eq_zero := rfl
  last_eq_horizon := rfl

def single (T : ℝ≥0) : TimePartition T where
  size := 1
  point := ![0, T]
  monotone_point := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first_eq_zero := rfl
  last_eq_horizon := rfl

@[simp] theorem mesh_empty : empty.mesh = 0 := by simp [mesh, empty]

def increment (π : TimePartition T) (f : ℝ≥0 → ℝ) (i : Fin π.size) : ℝ :=
  f (π.right i) - f (π.left i)

@[simp] theorem increment_const (π : TimePartition T) (c : ℝ) (i : Fin π.size) :
    π.increment (fun _ ↦ c) i = 0 := sub_self c

theorem increment_add (π : TimePartition T) (f g : ℝ≥0 → ℝ) (i : Fin π.size) :
    π.increment (f + g) i = π.increment f i + π.increment g i := by
  simp only [increment, Pi.add_apply]
  ring

theorem increment_mul (π : TimePartition T) (c : ℝ) (f : ℝ≥0 → ℝ) (i : Fin π.size) :
    π.increment (fun t ↦ c * f t) i = c * π.increment f i := by
  simp only [increment]
  ring

theorem sum_increment (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    (∑ i, π.increment f i) = f T - f 0 := by
  have h := (Fin.sum_univ_succ (fun i ↦ f (π.point i))).symm.trans
    (Fin.sum_univ_castSucc (fun i ↦ f (π.point i)))
  rw [π.first_eq_zero, π.last_eq_horizon] at h
  simp only [increment, right, left, sum_sub_distrib]
  linarith

theorem sum_gap (π : TimePartition T) : (∑ i, (π.gap i : ℝ)) = T := by
  have h := π.sum_increment (fun t ↦ (t : ℝ))
  simp only [increment, NNReal.coe_zero, sub_zero] at h
  simpa only [gap, NNReal.coe_sub (π.left_le_right _)] using h

end TimePartition

variable {T : ℝ≥0}

noncomputable def pVariationSum (p : ℝ) (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, |π.increment f i| ^ p

def quadraticVariationSum (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, (π.increment f i) ^ 2

def covariationSum (π : TimePartition T) (f g : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, π.increment f i * π.increment g i

def HasPVariationAlong (p : ℝ) (π : ℕ → TimePartition T)
    (f : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ pVariationSum p (π n) f) atTop (𝓝 value)

def HasQuadraticVariationAlong (π : ℕ → TimePartition T)
    (f : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ quadraticVariationSum (π n) f) atTop (𝓝 value)

def HasCovariationAlong (π : ℕ → TimePartition T)
    (f g : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ covariationSum (π n) f g) atTop (𝓝 value)

theorem quadraticVariationSum_nonneg (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    0 ≤ quadraticVariationSum π f := sum_nonneg fun _ _ ↦ sq_nonneg _

theorem pVariationSum_two (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pVariationSum 2 π f = quadraticVariationSum π f := by
  simp [pVariationSum, quadraticVariationSum, sq_abs]

@[simp] theorem quadraticVariationSum_const (π : TimePartition T) (c : ℝ) :
    quadraticVariationSum π (fun _ ↦ c) = 0 := by
  simp [quadraticVariationSum]

theorem quadraticVariationSum_single (T : ℝ≥0) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum (TimePartition.single T) f = (f T - f 0) ^ 2 := by
  change (∑ i : Fin 1, (f ((![0, T] : Fin 2 → ℝ≥0) i.succ) -
    f ((![0, T] : Fin 2 → ℝ≥0) i.castSucc)) ^ 2) = _
  rw [Fin.sum_univ_one]
  rfl

theorem covariationSum_single (T : ℝ≥0) (f g : ℝ≥0 → ℝ) :
    covariationSum (TimePartition.single T) f g = (f T - f 0) * (g T - g 0) := by
  change (∑ i : Fin 1, (f ((![0, T] : Fin 2 → ℝ≥0) i.succ) -
    f ((![0, T] : Fin 2 → ℝ≥0) i.castSucc)) *
    (g ((![0, T] : Fin 2 → ℝ≥0) i.succ) -
    g ((![0, T] : Fin 2 → ℝ≥0) i.castSucc))) = _
  rw [Fin.sum_univ_one]
  rfl

@[simp] theorem covariationSum_self (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    covariationSum π f f = quadraticVariationSum π f := by
  simp only [covariationSum, quadraticVariationSum, pow_two]

theorem covariationSum_comm (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    covariationSum π f g = covariationSum π g f := by
  simp only [covariationSum, mul_comm]

theorem covariationSum_add_left (π : TimePartition T) (f g h : ℝ≥0 → ℝ) :
    covariationSum π (f + g) h = covariationSum π f h + covariationSum π g h := by
  simp [covariationSum, TimePartition.increment_add, add_mul, sum_add_distrib]

theorem covariationSum_mul_left (π : TimePartition T) (c : ℝ) (f g : ℝ≥0 → ℝ) :
    covariationSum π (fun t ↦ c * f t) g = c * covariationSum π f g := by
  simp [covariationSum, TimePartition.increment_mul, mul_assoc, mul_sum]

theorem quadraticVariationSum_add (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    quadraticVariationSum π (f + g) = quadraticVariationSum π f +
      quadraticVariationSum π g + 2 * covariationSum π f g := by
  simp only [quadraticVariationSum, covariationSum, TimePartition.increment_add,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring

theorem covariationSum_polarization (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    covariationSum π f g =
      (quadraticVariationSum π (f + g) - quadraticVariationSum π f -
        quadraticVariationSum π g) / 2 := by
  rw [quadraticVariationSum_add]
  ring

theorem covariationSum_sq_le (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    (covariationSum π f g) ^ 2 ≤ quadraticVariationSum π f * quadraticVariationSum π g :=
  sum_mul_sq_le_sq_mul_sq _ _ _

theorem abs_covariationSum_le (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    |covariationSum π f g| ≤
      Real.sqrt (quadraticVariationSum π f) * Real.sqrt (quadraticVariationSum π g) := by
  have h := Real.le_sqrt_of_sq_le (covariationSum_sq_le π f g)
  rw [Real.sqrt_mul (quadraticVariationSum_nonneg π f)] at h
  have hneg := Real.le_sqrt_of_sq_le (show (-covariationSum π f g) ^ 2 ≤
      quadraticVariationSum π f * quadraticVariationSum π g by
    simpa only [neg_sq] using covariationSum_sq_le π f g)
  rw [Real.sqrt_mul (quadraticVariationSum_nonneg π f)] at hneg
  exact abs_le.mpr ⟨neg_le.mp hneg, h⟩

theorem HasQuadraticVariationAlong.nonneg {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    {a : ℝ} (hf : HasQuadraticVariationAlong π f a) : 0 ≤ a :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds hf fun n ↦ quadraticVariationSum_nonneg (π n) f

theorem HasQuadraticVariationAlong.unique {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    {a b : ℝ} (ha : HasQuadraticVariationAlong π f a) (hb : HasQuadraticVariationAlong π f b) :
    a = b := tendsto_nhds_unique ha hb

theorem HasQuadraticVariationAlong.covariation_zero_right {π : ℕ → TimePartition T}
    {f g : ℝ≥0 → ℝ} {a : ℝ} (hf : HasQuadraticVariationAlong π f a)
    (hg : HasQuadraticVariationAlong π g 0) : HasCovariationAlong π f g 0 := by
  have hb : Tendsto (fun n ↦ Real.sqrt (quadraticVariationSum (π n) f) *
      Real.sqrt (quadraticVariationSum (π n) g)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hf).mul
      (Real.continuous_sqrt.continuousAt.tendsto.comp hg)
  apply squeeze_zero_norm (fun n ↦ ?_) hb
  simpa only [Real.norm_eq_abs] using abs_covariationSum_le (π n) f g

/-- Pure pathwise zero-QV perturbation; the perturbation needs no semimartingale structure. -/
theorem HasQuadraticVariationAlong.add_zero {π : ℕ → TimePartition T}
    {f g : ℝ≥0 → ℝ} {a : ℝ} (hf : HasQuadraticVariationAlong π f a)
    (hg : HasQuadraticVariationAlong π g 0) : HasQuadraticVariationAlong π (f + g) a := by
  have hfg := hf.covariation_zero_right hg
  have h := (hf.add hg).add (hfg.const_mul 2)
  simpa only [HasQuadraticVariationAlong, ← quadraticVariationSum_add,
    show a + 0 + 2 * 0 = a by ring] using h

end StochLean
