module
public import ThreeRootOrder318

public section
noncomputable section
namespace NativeTensorScalar318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compatibility is proved for the native tensor module at an abstract base,
then specialized. The scalar action is not replaced by an asserted definitional equality. -/
theorem tensor_smul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (r : R) (z : A ⊗[R] B) :
    r • z = algebraMap R (A ⊗[R] B) r * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero,mul_zero]
  | tmul a b =>
    rw [TensorProduct.smul_tmul',Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul]
    all_goals exact congrArg (fun a : A => a ⊗ₜ[R] b) (Algebra.smul_def r a)
  | add x y hx hy =>
    simpa only [smul_add,mul_add,hx,hy]

/-- The original three-root order carries this exact native base action. -/
theorem three_smul {R : Type*} [CommRing R] (a : Fin 3 → R) (r : R)
    (z : ThreeRootOrder318.Order a) : r • z = algebraMap R (ThreeRootOrder318.Order a) r * z :=
  tensor_smul r z

end NativeTensorScalar318
