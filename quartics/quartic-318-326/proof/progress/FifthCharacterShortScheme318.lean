module
public import FifthCharacterShortCoordinates318
public import RationalSchemePointGroup318
public section
noncomputable section
namespace FifthCharacterShortScheme318
open AlgebraicGeometry CategoryTheory
open FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def cubic : Scheme:=Spec (CommRingCat.of CubicRing)
@[expose] def cubicBase : cubic ⟶ Spec (CommRingCat.of ℚ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ CubicRing))
/-- Whole affine reciprocal-cubic to literal short-model isomorphism.
This does not identify the whole original quartic affine chart with it. -/
@[expose] def affineIso : cubic ≅ ShortAffineScheme318.scheme A B:=
  (Scheme.Spec.mapIso coordinateEquiv.toRingEquiv.toCommRingCatIso.op).symm
@[reassoc] theorem affineIso_over_Q : affineIso.hom ≫ ShortAffineScheme318.structureMap A B=cubicBase:=by
  change Spec.map (CommRingCat.ofHom coordinateEquiv.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact coordinateEquiv.symm.commutes q
@[expose] def completed : Scheme:=WeierstrassGluing318.scheme A B
@[expose] def intoCompleted : cubic ⟶ completed:=affineIso.hom ≫ WeierstrassGluing318.finiteChart A B
/-- The chosen elliptic zero of the actual short completion is [0:1:0].
A later completed quartic comparison must check its source preimage. -/
@[expose] def zero : Spec (CommRingCat.of ℚ) ⟶ completed:=WeierstrassGluing318.infinity A B
@[reassoc] theorem intoCompleted_over_Q :
    intoCompleted ≫ WeierstrassGluing318.structureMap A B=cubicBase:=by
  rw [intoCompleted,Category.assoc,WeierstrassGluing318.finiteChart_structure,affineIso_over_Q]
/-- The already proved rational Scheme group applies to these exact
nonsingular coefficients, with no literal-family ratio substitution. -/
theorem associative : CompletedAdditionTriple318.leftAssociate A B discriminant_unit=
    CompletedAdditionTriple318.rightAssociate A B discriminant_unit:=
  RationalGroupAssociativity318.associative A B discriminant_unit
abbrev Points {T:Scheme} (b:T ⟶ Spec (CommRingCat.of ℚ)):=
  RationalSchemePointOperations318.Points A B discriminant_unit b
@[expose] def group {T:Scheme} (b:T ⟶ Spec (CommRingCat.of ℚ)) : AddCommGroup (Points b):=
  RationalSchemePointGroup318.group A B discriminant_unit b
@[simp] theorem zero_value {T:Scheme} (b:T ⟶ Spec (CommRingCat.of ℚ)) :
    (0:Points b).val=b ≫ zero:=rfl
end FifthCharacterShortScheme318
