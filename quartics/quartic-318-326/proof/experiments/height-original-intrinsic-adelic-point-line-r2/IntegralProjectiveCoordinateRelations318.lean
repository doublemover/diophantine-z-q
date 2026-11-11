module
public import ClutchedCoordinateRelations318
public import IntegralProjectiveCoordinateFrames318
public section
noncomputable section
namespace IntegralProjectiveCoordinateRelations318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralProjectiveLineOverlap318 IntegralProjectiveLineOOne318 IntegralProjectiveLineCoordinates318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
/-- The exact local ratio identity q1=t*q0 on the entire finite target chart. -/
@[expose] def finite_relation := ClutchedCoordinateRelations318.first_relation
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (coordinate R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (zero_compatible R) (one_compatible R)
  (transition_unit R) (infinity_intersection R) (coordinate R) (mul_one (coordinate R)).symm
/-- The exact local ratio identity q0=s*q1 on the entire infinity target chart. -/
@[expose] def infinity_relation := ClutchedCoordinateRelations318.second_relation
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤))
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (one_compatible R) (zero_compatible R)
  (finite_intersection R) (coordinate R) (mul_one (coordinate R)).symm
end IntegralProjectiveCoordinateRelations318
