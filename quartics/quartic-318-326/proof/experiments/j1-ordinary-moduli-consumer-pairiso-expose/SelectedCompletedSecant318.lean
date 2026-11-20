module
public import SelectedSecantSchematicDensity318
public import CompletedCoefficientProduct318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318

namespace SelectedCompletedSecant318
variable {R : Type u} [CommRing R] (A B : R)

/-- The actual ordinary secant open inside the completed pair scheme,
not a chart identified only on field-valued points. -/
@[expose] def intoPair : RelativeChordScheme318.chordOpen A B ⟶
    pullback (structureMap A B) (structureMap A B) :=
  RelativeChordScheme318.intoProduct A B ≫ FiniteProductSchematicDensity318.pairMap A B

theorem dense (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    IsSchemeTheoreticallyDominant (intoPair A B) := by
  letI := SelectedSecantSchematicDensity318.dense A B
  letI := FiniteProductSchematicDensity318.pairMap_dense A B hD
  unfold intoPair
  infer_instance

/-- This is the exact original completed addition on the new dense
test. The output is the actual chord map followed by the finite chart. -/
theorem completed_addition_restrict (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    intoPair A B ≫ CompletedAddition318.addition A B hD =
      RelativeChordScheme318.addition A B ≫ finiteChart A B := by
  rw [intoPair,Category.assoc,CompletedCoefficientProduct318.finite_restriction]
  have h := FiniteAdditionGluing318.restriction A B hD (0 : Fin 4)
  rw [FinitePairSchemeCover318.productCover_chord] at h
  exact h

/-- On the actual completed square, it now suffices to compare relative
maps on the ordinary secant open. No domain or field-point premise. -/
theorem maps_ext (A' B' : R) (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (f g : pullback (structureMap A B) (structureMap A B) ⟶ scheme A' B')
    (hbase : f ≫ structureMap A' B' = g ≫ structureMap A' B')
    (hsecant : intoPair A B ≫ f = intoPair A B ≫ g) : f = g := by
  letI := dense A B hD
  letI := CubicClosedImmersion318.structure_proper A' B'
  exact SchematicEqualityExtension318.ext (structureMap A' B') hbase (intoPair A B) hsecant

end SelectedCompletedSecant318

#print axioms SelectedCompletedSecant318.completed_addition_restrict
#print axioms SelectedCompletedSecant318.maps_ext
