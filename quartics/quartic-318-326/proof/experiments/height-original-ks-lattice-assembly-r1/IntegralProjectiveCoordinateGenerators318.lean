module
public import ClutchedCoordinateGenerators318
public import IntegralProjectiveCoordinateFrames318
public section
noncomputable section
namespace IntegralProjectiveCoordinateGenerators318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralProjectiveLineOverlap318 IntegralProjectiveLineOOne318 IntegralProjectiveLineCoordinates318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
/-- The actual first coordinate morphism freely generates on the entire finite chart. -/
@[expose] def zero_finite_isIso := ClutchedCoordinateGenerators318.first_isIso
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
  (transition_unit R) (infinity_intersection R) isUnit_one
/-- The actual second coordinate morphism freely generates on the entire infinity chart. -/
@[expose] def one_infinity_isIso := ClutchedCoordinateGenerators318.second_isIso
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R) (finite_intersection R) isUnit_one
end IntegralProjectiveCoordinateGenerators318
