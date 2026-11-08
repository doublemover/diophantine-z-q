module
public import RationalAssociativityTest318
public import RationalProductReduced318
public import CubicClosedImmersion318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace RationalGroupAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CompletedAdditionTriple318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Actual global associativity for EVERY nonsingular rational short
Weierstrass model, with no OpenJ coefficient-ratio or twist premise. -/
theorem associative (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    leftAssociate A B hD=rightAssociate A B hD:=by
  haveI:=RationalProductReduced318.triple_reduced A B
  haveI:=CubicClosedImmersion318.structure_proper A B
  apply AlgebraicGeometry.ext_of_fromSpecResidueField_eq _ _
    (WeierstrassGluing318.structureMap A B) Set.univ dense_univ
  · intro x _
    let t:Spec ((triple A B).residueField x) ⟶ triple A B:=(triple A B).fromSpecResidueField x
    obtain ⟨b,hb⟩:=Spec.map_surjective (t ≫ first A B ≫ WeierstrassGluing318.structureMap A B)
    letI:Algebra ℚ ((triple A B).residueField x):=b.hom.toAlgebra
    exact RationalAssociativityTest318.field_test A B hD (K:=((triple A B).residueField x)) t hb.symm
  · rw [leftAssociate_base,rightAssociate_base]
end RationalGroupAssociativity318
