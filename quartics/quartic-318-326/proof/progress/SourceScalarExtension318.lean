module
public import PolynomialScalarExtension318
public import ContactGeometricOrder318
public section
noncomputable section
namespace SourceScalarExtension318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Polynomial.algebra
variable (F:Type u) [Field F] [CharZero F] [Algebra ℚ F] (c:Fin 4→ℚˣ)
abbrev Original:=ContactKummerOrder318.SourceOrder c
local instance originalCommRing : CommRing (Original c):=inferInstance
local instance originalAlgebra : Algebra ℚ (Original c):=inferInstance

/-- The genuine rational scalar extension is the actual polynomial-base
extension; this is an isomorphism of the full tensor rings. -/
@[expose] def reassociate : F⊗[ℚ]Original c≃ₐ[ℚ]F[X]⊗[ℚ[X]]Original c:=
  (Algebra.TensorProduct.comm ℚ F (Original c)).trans
    ((Algebra.TensorProduct.congr
      ((Algebra.TensorProduct.rid ℚ[X] ℚ[X] (Original c)).symm.restrictScalars ℚ)
      (AlgEquiv.refl : F≃ₐ[ℚ]F)).trans
    (((Algebra.TensorProduct.assoc ℚ ℚ[X] ℚ[X] (Original c) ℚ[X] F).restrictScalars ℚ).trans
    (((Algebra.TensorProduct.congr (AlgEquiv.refl : Original c≃ₐ[ℚ[X]]Original c)
      (PolynomialScalarExtension318.rightEquiv F)).restrictScalars ℚ).trans
      ((Algebra.TensorProduct.comm ℚ[X] (Original c) F[X]).restrictScalars ℚ))))

lemma coefficient_map (i:Fin 4) :
    algebraMap ℚ[X] F[X] (ContactKummerOrder318.coefficient c i)=
      ContactGeometricOrder318.coefficient F c i:=by
  simp [ContactKummerOrder318.coefficient,ContactGeometricOrder318.coefficient,
    ContactGeometricOrder318.contacts,Polynomial.algebraMap_def]

@[expose] def orderParameterEquiv {R:Type*} [CommRing R] {a b:Fin 4→R}
    (h:a=b) : FourRootOrder318.Order a≃ₐ[R]FourRootOrder318.Order b:=by
  subst b
  exact AlgEquiv.refl

@[expose] def polynomialBaseChange : F[X]⊗[ℚ[X]]Original c≃ₐ[F[X]]ContactGeometricOrder318.Order F c:=by
  have he:(fun i=>algebraMap ℚ[X] F[X] (ContactKummerOrder318.coefficient c i))=
      ContactGeometricOrder318.coefficient F c:=funext (coefficient_map F c)
  exact (FourRootOrder318.baseChange (ContactKummerOrder318.coefficient c) F[X]).trans
    (orderParameterEquiv he)

/-- Actual scalar extension of the original entire source, not merely an
isomorphic-looking presentation with changed constants. -/
@[expose] def scalarExtensionEquiv : F⊗[ℚ]Original c≃+*ContactGeometricOrder318.Order F c:=
  (reassociate F c).toRingEquiv.trans (polynomialBaseChange F c).toRingEquiv

lemma scalarExtension_domain : IsDomain (F⊗[ℚ]Original c):=by
  letI:=ContactGeometricOrder318.order_domain F c
  exact Function.Injective.isDomain (scalarExtensionEquiv F c).toRingHom
    (scalarExtensionEquiv F c).injective
end SourceScalarExtension318
