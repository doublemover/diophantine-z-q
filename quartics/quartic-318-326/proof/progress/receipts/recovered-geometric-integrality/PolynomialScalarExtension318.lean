module
public import Mathlib.RingTheory.PolynomialAlgebra
public section
noncomputable section
namespace PolynomialScalarExtension318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (F:Type u) [CommRing F] [Algebra ℚ F]

attribute [local instance] Polynomial.algebra

@[expose] def leftEquiv : F⊗[ℚ]ℚ[X]≃ₐ[F]F[X]:=
  (polyEquivTensor' ℚ F).symm

lemma leftEquiv_X : leftEquiv F ((1:F)⊗ₜ[ℚ](X:ℚ[X]))=(X:F[X]):=by
  simp [leftEquiv]
lemma leftEquiv_C (q:ℚ) : leftEquiv F ((1:F)⊗ₜ[ℚ]C q)=C (algebraMap ℚ F q):=by
  simp [leftEquiv]
lemma leftEquiv_polynomial (p:ℚ[X]) :
    leftEquiv F ((1:F)⊗ₜ[ℚ]p)=algebraMap ℚ[X] F[X] p:=by
  simp [leftEquiv,Polynomial.algebraMap_def]

/-- Scalar extension of the polynomial coefficient ring, preserving its
original polynomial-variable map. -/
@[expose] def rightEquiv : ℚ[X]⊗[ℚ]F≃ₐ[ℚ[X]]F[X]:=
  { (Algebra.TensorProduct.comm ℚ ℚ[X] F).toRingEquiv.trans (leftEquiv F).toRingEquiv with
    commutes':=by intro p;exact leftEquiv_polynomial F p }
end PolynomialScalarExtension318
