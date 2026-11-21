/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra
public import StochLean.Probability.Process.Path.LeftLimit
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Complex paths as pairs of the existing real coordinate processes

The source left limit is zero at time zero. At positive times it is
the actual strict-left complex limit whenever the path is cadlag.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

def complexProcess {T Ω : Type*} (X Y : T → Ω → ℝ) : T → Ω → ℂ := fun t ω ↦
  ⟨X t ω, Y t ω⟩

@[simp] theorem complexProcess_re {T Ω : Type*} (X Y : T → Ω → ℝ) (t : T) (ω : Ω) :
    (complexProcess X Y t ω).re = X t ω := rfl

@[simp] theorem complexProcess_im {T Ω : Type*} (X Y : T → Ω → ℝ) (t : T) (ω : Ω) :
    (complexProcess X Y t ω).im = Y t ω := rfl

theorem HasCadlagPaths.complex {T Ω : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → ℝ}
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) :
    HasCadlagPaths (complexProcess X Y) P := by
  have h := (hX.continuous_comp Complex.continuous_ofReal).add
    (hY.continuous_comp (continuous_const.mul Complex.continuous_ofReal :
      Continuous (fun y : ℝ ↦ Complex.I * (y : ℂ))))
  apply HasCadlagPaths.congr _ h
  exact ae_of_all _ (fun ω t ↦ by apply Complex.ext <;> simp [complexProcess])

theorem HasCagladPaths.complex {T Ω : Type*} [LinearOrder T] [TopologicalSpace T]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → ℝ}
    (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) :
    HasCagladPaths (complexProcess X Y) P := by
  have h := (hX.continuous_comp Complex.continuous_ofReal).add
    (hY.continuous_comp (continuous_const.mul Complex.continuous_ofReal :
      Continuous (fun y : ℝ ↦ Complex.I * (y : ℂ))))
  apply HasCagladPaths.congr _ h
  exact ae_of_all _ (fun ω t ↦ by apply Complex.ext <;> simp [complexProcess])

noncomputable def complexLeftLimitProcess {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  complexProcess (leftLimitProcess (fun t ω ↦ (Z t ω).re))
    (leftLimitProcess (fun t ω ↦ (Z t ω).im))

@[simp] theorem complexLeftLimitProcess_zero {Ω : Type*} (Z : ℝ≥0 → Ω → ℂ) :
    complexLeftLimitProcess Z 0 = 0 := by
  funext ω
  apply Complex.ext <;> simp [complexLeftLimitProcess, complexProcess]

theorem IsCadlagPath.complexLeftLimitProcess_eq_leftLim {Ω : Type*}
    {Z : ℝ≥0 → Ω → ℂ} {ω : Ω} (hZ : IsCadlagPath (Z · ω)) {t : ℝ≥0} (ht : 0 < t) :
    complexLeftLimitProcess Z t ω = Function.leftLim (Z · ω) t := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlim := tendsto_leftLim_of_tendsto (hZ.2 t (ne_of_gt ht))
  apply Complex.ext
  · change leftLimitProcess (fun u v ↦ (Z u v).re) t ω = _
    rw [leftLimitProcess, if_neg (ne_of_gt ht)]
    exact leftLim_eq_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim)
  · change leftLimitProcess (fun u v ↦ (Z u v).im) t ω = _
    rw [leftLimitProcess, if_neg (ne_of_gt ht)]
    exact leftLim_eq_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hlim)

end ProbabilityTheory
