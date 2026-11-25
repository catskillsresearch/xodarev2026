module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word


@[expose] public section

namespace SignatureVolatility

/-- **Definition 2.3 (Extended tensor algebra)**: `T((ℝ^d)) = ∏_{n ≥ 0} (ℝ^d)^{⊗ n}`,
represented via word-indexed formal series. -/
@[ext]
structure ExtTensorAlgebra (d : ℕ) where
  coeff : Word d → ℝ

namespace ExtTensorAlgebra

/-- Zero series: every coefficient is `0`. -/
instance {d : ℕ} : Zero (ExtTensorAlgebra d) := ⟨⟨fun _ => 0⟩⟩
/-- Coefficientwise addition. -/
instance {d : ℕ} : Add (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I + b.coeff I⟩⟩
/-- Coefficientwise negation. -/
instance {d : ℕ} : Neg (ExtTensorAlgebra d) := ⟨fun a => ⟨fun I => -a.coeff I⟩⟩
/-- Coefficientwise subtraction. -/
instance {d : ℕ} : Sub (ExtTensorAlgebra d) := ⟨fun a b => ⟨fun I => a.coeff I - b.coeff I⟩⟩
/-- Coefficientwise real scalar multiplication. -/
instance {d : ℕ} : SMul ℝ (ExtTensorAlgebra d) := ⟨fun c a => ⟨fun I => c * a.coeff I⟩⟩

/-- The coefficientwise additive group structure. -/
instance {d : ℕ} : AddCommGroup (ExtTensorAlgebra d) where
  add_assoc a b c := by ext I; exact add_assoc _ _ _
  zero_add a := by ext I; exact zero_add _
  add_zero a := by ext I; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext I; exact neg_add_cancel _
  add_comm a b := by ext I; exact add_comm _ _

/-- The coefficientwise real vector-space structure. -/
instance {d : ℕ} : Module ℝ (ExtTensorAlgebra d) where
  one_smul a := by ext I; exact one_mul _
  mul_smul r s a := by ext I; exact mul_assoc _ _ _
  smul_zero r := by ext I; exact mul_zero _
  smul_add r a b := by ext I; exact mul_add _ _ _
  add_smul r s a := by ext I; exact add_mul _ _ _
  zero_smul a := by ext I; exact zero_mul _

end ExtTensorAlgebra

end SignatureVolatility
