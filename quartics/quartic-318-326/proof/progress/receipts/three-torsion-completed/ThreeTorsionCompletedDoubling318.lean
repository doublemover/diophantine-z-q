module
public import CompletedTangentRestriction318
public import ThreeTorsionTangentScheme318
public import GluedNegation318
public section
noncomputable section
namespace ThreeTorsionCompletedDoubling318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The exact inclusion of the existing full rank-eight algebra in the completed curve. -/
@[expose] def inclusion : ThreeTorsionScheme318.scheme A B hD⟶WeierstrassGluing318.scheme A B :=
  ThreeTorsionScheme318.inclusion A B hD ≫ WeierstrassGluing318.finiteChart A B

@[reassoc] theorem inclusion_over_base : inclusion A B hD ≫ WeierstrassGluing318.structureMap A B =
    ThreeTorsionScheme318.structureMap A B hD := by
  rw [inclusion,Category.assoc,WeierstrassGluing318.finiteChart_structure,
    ThreeTorsionScheme318.inclusion_over_base]

/-- The literal tangent equality is now the actual completed doubling equality,
not just a polynomial equation or a field-point assertion. -/
theorem doubling_eq_negation :
    inclusion A B hD ≫ CompletedIteratedAddition318.doubling A B hD =
      inclusion A B hD ≫ GluedNegation318.negation A B := by
  rw [inclusion,Category.assoc]
  rw [CompletedTangentRestriction318.doubling_restriction A B hD
    (ThreeTorsionScheme318.inclusion A B hD) (ThreeTorsionTangentScheme318.diagonal A B hD)
    (ThreeTorsionTangentScheme318.diagonal_intoProduct A B hD)]
  rw [←Category.assoc,ThreeTorsionTangentScheme318.double_neg,Category.assoc]
  change ThreeTorsionScheme318.inclusion A B hD ≫ GluedNegation318.finiteNeg A B ≫
      WeierstrassGluing318.finiteChart A B =
    (ThreeTorsionScheme318.inclusion A B hD ≫ WeierstrassGluing318.finiteChart A B) ≫
      GluedNegation318.negation A B
  rw [Category.assoc,GluedNegation318.finiteChart_negation]
end ThreeTorsionCompletedDoubling318
