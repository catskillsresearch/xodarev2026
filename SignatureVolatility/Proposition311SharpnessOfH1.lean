module

public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.SuperfactorialFunctional
public import SignatureVolatility.Weight


@[expose] public section

open Filter Topology

noncomputable section

namespace SignatureVolatility

theorem proposition_3_11_sharpness_of_H1 {α : ℝ} (hα : 0 < α) :
    (∀ (w : Weight), HypH2 w → ¬ HypH1 w (superfactorialFunctional α)) ∧
    (∀ (x : ℝ), 1 ≤ α * |x| →
      ¬ Summable (fun n : ℕ => ((n.factorial : ℝ) * α ^ n) * (x ^ n / (n.factorial : ℝ)))) := by
  refine ⟨fun w hw h1 => ?_, fun x hx hsum => ?_⟩
  · have hsub := hw.subfactorial (α⁻¹) (inv_pos.mpr hα)
    have htend0 := hsub.tendsto_atTop_zero
    have htend1 := h1.mem_l2w.tendsto_atTop_zero
    have hprod : Tendsto (fun n : ℕ =>
        (w n * ((α⁻¹) ^ n / (n.factorial : ℝ))) ^ 2 *
          ((superfactorialFunctional α).levelNormSq n / (w n) ^ 2)) atTop (𝓝 0) := by
      simpa using (htend0.pow 2).mul htend1
    have hconst : (fun n : ℕ =>
        (w n * ((α⁻¹) ^ n / (n.factorial : ℝ))) ^ 2 *
          ((superfactorialFunctional α).levelNormSq n / (w n) ^ 2)) = fun _ => (1 : ℝ) := by
      ext n
      rw [superfactorialFunctional.levelNormSq]
      have hw_ne : w n ≠ 0 := (w.pos n).ne'
      have hfac_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hα_ne : α ≠ 0 := hα.ne'
      rw [inv_pow]
      field_simp [hw_ne, hfac_ne, hα_ne]
    rw [hconst] at hprod
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hprod)
  · have hsimp : (fun n : ℕ => ((n.factorial : ℝ) * α ^ n) * (x ^ n / (n.factorial : ℝ))) =
        fun n : ℕ => (α * x) ^ n := by
      ext n
      have hfac_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      rw [mul_pow]
      field_simp [hfac_ne]
    rw [hsimp] at hsum
    have habs_lt : |α * x| < 1 := summable_geometric_iff_norm_lt_one.mp hsum
    rw [abs_mul, abs_of_pos hα] at habs_lt
    linarith

end SignatureVolatility
