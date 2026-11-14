module
public import LocalSectionCommonChart318
public import IntegralEtaleCotangent318
public import AffineSectionCotangentImage318
public section
noncomputable section
namespace LocalSectionCotangentComparison318
open AlgebraicGeometry CategoryTheory AffineSectionCotangentImage318
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {g : Spec (CommRingCat.of R) ⟶ X}
  (A B : LocalSectionAffineChart318.Data f g)
  (C : LocalSectionCommonChart318.Common A B)

/-- This is an integral-module comparison at the same section. The
exact differential law retains functions on the actual common chart. -/
structure Data where
  equiv : Cotangent A ≃ₗ[R] Cotangent B
  differential : ∀ (a : A.ring) (b : B.ring), C.left.hom a = C.right.hom b →
    equiv (AffineSectionCotangentImage318.differential A a) =
      AffineSectionCotangentImage318.differential B b

/-- All point-dependent algebras are explicit local bindings. No
instance registration is asked to recover a section from its target. -/
@[expose] def data : Data A B C := by
  letI : Algebra R A.ring := A.scalar.hom.toAlgebra
  letI : Algebra R B.ring := B.scalar.hom.toAlgebra
  letI : Algebra A.ring R := A.evaluation.hom.toAlgebra
  letI : Algebra B.ring R := B.evaluation.hom.toAlgebra
  letI : Algebra A.ring C.ring := C.left.hom.toAlgebra
  letI : Algebra B.ring C.ring := C.right.hom.toAlgebra
  letI : Algebra R C.ring := (C.left.hom.comp A.scalar.hom).toAlgebra
  letI : Algebra C.ring R := C.evaluation.hom.toAlgebra
  letI : IsScalarTower R A.ring C.ring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R B.ring C.ring :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      congrArg (fun h => h.hom r) (LocalSectionCommonChart318.scalar_square A B C))
  letI : IsScalarTower A.ring C.ring R :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (congrArg (fun h => h.hom a) C.left_point).symm)
  letI : IsScalarTower B.ring C.ring R :=
    IsScalarTower.of_algebraMap_eq (fun b =>
      (congrArg (fun h => h.hom b) C.right_point).symm)
  letI : Algebra.Etale A.ring C.ring := RingHom.etale_algebraMap.mp C.left_etale
  letI : Algebra.Etale B.ring C.ring := RingHom.etale_algebraMap.mp C.right_etale
  exact ⟨IntegralEtaleCotangent318.comparison R A.ring C.ring R B.ring,
    fun a b h => IntegralEtaleCotangent318.comparison_differential
      R A.ring C.ring R B.ring a b h⟩

@[expose] def comparison : Cotangent A ≃ₗ[R] Cotangent B := (data A B C).equiv

theorem comparison_differential (a : A.ring) (b : B.ring)
    (h : C.left.hom a = C.right.hom b) :
    comparison A B C (AffineSectionCotangentImage318.differential A a) =
      AffineSectionCotangentImage318.differential B b :=
  (data A B C).differential a b h
end LocalSectionCotangentComparison318
