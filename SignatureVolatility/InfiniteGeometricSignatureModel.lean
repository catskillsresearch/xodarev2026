import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.HypH2
import SignatureVolatility.Weight.Geometric
import SignatureVolatility.MemL2w
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def infiniteGeometricSignatureModel (d : ℕ) (hd : 0 < d) (T s₀ r q C : ℝ)
    (hT : 0 < T) (hs₀ : 0 < s₀) (hr : 1 ≤ r) (hq0 : 0 ≤ q) (hqr : q < r) (hC : 0 ≤ C)
    (ℓ : ExtTensorAlgebra (d + 1)) (hnz : ℓ ≠ 0)
    (hdecay : ∀ n : ℕ, ℓ.levelNorm n ≤ C * q ^ n) : SignatureVolatilityModel where
  d := d
  hd := hd
  T := T
  hT := hT
  w := Weight.geometric r hr
  ℓ := ℓ
  s₀ := s₀
  hs₀ := hs₀
  h1 := ⟨by
    have hr_pos : 0 < r := zero_lt_one.trans_le hr
    have hratio0 : 0 ≤ (q / r) ^ 2 := sq_nonneg _
    have hratio1 : (q / r) ^ 2 < 1 := by
      have hdiv_lt : q / r < 1 := (div_lt_one hr_pos).mpr hqr
      have hdiv_nonneg : 0 ≤ q / r := div_nonneg hq0 hr_pos.le
      nlinarith
    have hgeom : Summable (fun n : ℕ => C ^ 2 * ((q / r) ^ 2) ^ n) :=
      (summable_geometric_of_lt_one hratio0 hratio1).mul_left (C ^ 2)
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg ℓ n) (sq_nonneg _)) (fun n => ?_) hgeom
    rw [← ExtTensorAlgebra.levelNorm.sq ℓ]
    have hle : ℓ.levelNorm n / (Weight.geometric r hr n) ≤ C * (q / r) ^ n := by
      simp only [Weight.geometric]
      rw [div_pow]
      calc
        ℓ.levelNorm n / r ^ n ≤ (C * q ^ n) / r ^ n :=
          div_le_div_of_nonneg_right (hdecay n) (pow_nonneg hr_pos.le n)
        _ = C * (q ^ n / r ^ n) := mul_div_assoc _ _ _
    have h0 : 0 ≤ ℓ.levelNorm n / (Weight.geometric r hr n) :=
      div_nonneg (ExtTensorAlgebra.levelNorm.nonneg ℓ n) (pow_nonneg hr_pos.le n)
    have hsq := pow_le_pow_left₀ h0 hle 2
    calc
      (ℓ.levelNorm n) ^ 2 / (Weight.geometric r hr n) ^ 2
          = (ℓ.levelNorm n / Weight.geometric r hr n) ^ 2 := (div_pow _ _ 2).symm
      _ ≤ (C * (q / r) ^ n) ^ 2 := hsq
      _ = C ^ 2 * ((q / r) ^ 2) ^ n := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]⟩
  h2 := HypH2.geometric_admissible r hr
  h3 := ⟨hnz⟩

end SignatureVolatility
