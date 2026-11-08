module
public import ClutchedCoordinateRelations318
public import ProjectiveLineCoordinateFrames318
public section
noncomputable section
namespace ProjectiveLineCoordinateRelations318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ProjectiveLineOOne318 ProjectiveLineCoordinates318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- The exact local ratio identity q1=t*q0 on the entire finite target chart. -/
@[expose] def finite_relation := ClutchedCoordinateRelations318.first_relation
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate coordinate
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) zero_compatible one_compatible
  transition_unit infinity_intersection coordinate (mul_one coordinate).symm
/-- The exact local ratio identity q0=s*q1 on the entire infinity target chart. -/
@[expose] def infinity_relation := ClutchedCoordinateRelations318.second_relation
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤))
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate one_compatible zero_compatible
  finite_intersection coordinate (mul_one coordinate).symm
end ProjectiveLineCoordinateRelations318
