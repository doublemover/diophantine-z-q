module
public import ContactRelativeStructuralHOne318
public section
noncomputable section
namespace ContactOriginalCoefficientActions318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
@[expose] def finiteModule : Module R (finiteSections R c L) :=
  Module.compHom _ Polynomial.C
@[expose] def infinityModule : Module R (infinitySections R c L) :=
  Module.compHom _ Polynomial.C
@[expose] def overlapLaurentModule : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
@[expose] def overlapModule : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R _
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L

abbrev structuralFinite := (ModuleCat.restrictScalars (algebraMap R (R ⊗[ℚ] finiteRing c))).obj
  (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] finiteRing c)) (finiteLine R c L))
abbrev structuralInfinity := (ModuleCat.restrictScalars (algebraMap R (R ⊗[ℚ] infinityRing c))).obj
  (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] infinityRing c)) (infinityLine R c L))
abbrev structuralOverlap := (ModuleCat.restrictScalars (algebraMap R (ring R c))).obj
  (OriginalLineAffineModel318.sections (ring R c) (line R c L))

/-- Identity on the SAME original finite sections, with the actual
polynomial-C coefficient action reconciled with structural restriction. -/
@[expose] def finiteIdentity : finiteSections R c L ≃ₗ[R] structuralFinite R c L where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (finiteRing c)
      (Polynomial.C r) • x = algebraMap R (R ⊗[ℚ] finiteRing c) r • x
    rw [RelativeOriginalPolynomialAlgebra318.polynomialMap_C]
    rfl

@[expose] def infinityIdentity : infinitySections R c L ≃ₗ[R] structuralInfinity R c L where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c)
      (Polynomial.C r) • x = algebraMap R (R ⊗[ℚ] infinityRing c) r • x
    rw [RelativeOriginalPolynomialAlgebra318.polynomialMap_C]
    rfl

/-- Identity on the SAME original overlap, using the previously proved
actual Laurent-C map. This does not transport a new action onto H1. -/
@[expose] def overlapIdentity : originalSections R c L ≃ₗ[R] structuralOverlap R c L where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (C r) • x =
      algebraMap R (ring R c) r • x
    rw [RelativeOriginalLaurentAlgebra318.laurentMap_C]
    rfl
end ContactOriginalCoefficientActions318
