module
public import ClutchedCoordinateFrames318
public import IntegralProjectiveLineCoordinates318
public section
noncomputable section
namespace IntegralProjectiveCoordinateFrames318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralProjectiveLineOverlap318 IntegralProjectiveLineOOne318 IntegralProjectiveLineCoordinates318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
/-- Exact finite-frame value of the actual first global coordinate. -/
@[expose] def q0_finite := ClutchedCoordinateFrames318.first_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
  (transition_unit R) (infinity_intersection R)
/-- Exact infinity-frame value of the actual first global coordinate. -/
@[expose] def q0_infinity := ClutchedCoordinateFrames318.second_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R) (finite_intersection R)
/-- Exact finite-frame value of the actual second global coordinate. -/
@[expose] def q1_finite := ClutchedCoordinateFrames318.first_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R)
  (transition_unit R) (infinity_intersection R)
/-- Exact infinity-frame value of the actual second global coordinate. -/
@[expose] def q1_infinity := ClutchedCoordinateFrames318.second_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R) (finite_intersection R)
end IntegralProjectiveCoordinateFrames318
