module
public import FiniteDualModuleAction318
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public section
noncomputable section
namespace FiniteDualTransport318
open FiniteDualModuleAction318
open scoped TensorProduct
set_option maxHeartbeats 1800000
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B)

/-- Actual precomposition on the entire finite dual, semilinear for the
whole order isomorphism and its multiplication action. -/
@[expose] def transport : Dual R A →ₛₗ[e.toRingEquiv.toRingHom] Dual R B where
  toFun f := f.comp e.symm.toLinearMap
  map_add' f g := rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro b
    change f (a*e.symm b)=f (e.symm (e a*b))
    rw [map_mul,e.symm_apply_apply]

theorem transport_apply (f : Dual R A) (b : B) :
    evaluate R B (transport e f) b=evaluate R A f (e.symm b) := rfl

abbrev Square := Dual R A ⊗[A] Dual R A

/-- Balanced map out of the WHOLE tensor square of the true finite dual.
This is not merely a formula on pairs of chosen generators. -/
@[expose] def squareTransport : Square (R:=R) (A:=A) →ₛₗ[e.toRingEquiv.toRingHom]
    Square (R:=R) (A:=B) := TensorProduct.map (transport e) (transport e)

theorem squareTransport_pure (f g : Dual R A) :
    squareTransport e (f ⊗ₜ[A] g)=transport e f ⊗ₜ[B] transport e g := rfl

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (F : TensorCoefficientDuality318.Frame R A ι)
  (G : TensorCoefficientDuality318.Frame R B κ)

@[expose] def squareFrame : A ≃ₗ[A] Square (R:=R) (A:=A) :=
  (TensorProduct.lid A A).symm.trans
    (TensorProduct.congr (frame R A F) (frame R A F))

theorem squareFrame_one : squareFrame F 1=frame R A F 1 ⊗ₜ[A] frame R A F 1 := rfl

theorem squareFrame_scalar (a : A) : squareFrame F a=a • squareFrame F 1 := by
  rw [←map_smul]
  simp only [smul_eq_mul,mul_one]

/-- Exact transition of every tensor-square section from the actual
transition of its dual generator and the whole semilinear tensor map. -/
theorem squareTransport_frame (λ : B)
    (hλ : transport e (frame R A F 1)=λ • frame R B G 1) (a : A) :
    squareTransport e (squareFrame F a)=
      squareFrame G (e a*λ^2) := by
  rw [squareFrame_scalar,map_smul,squareFrame_one,squareTransport_pure,hλ,
    TensorProduct.smul_tmul_smul,←squareFrame_one,smul_smul]
  rw [squareFrame_scalar]
  congr 1
  ring
end FiniteDualTransport318
