module
public import ClutchedCoordinateFrames318
public import ProjectiveLineCoordinates318
public section
noncomputable section
namespace ProjectiveLineCoordinateFrames318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ProjectiveLineOOne318 ProjectiveLineCoordinates318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Exact finite-frame value of the actual first global coordinate. -/
@[expose] def q0_finite := ClutchedCoordinateFrames318.first_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
  transition_unit infinity_intersection
/-- Exact infinity-frame value of the actual first global coordinate. -/
@[expose] def q0_infinity := ClutchedCoordinateFrames318.second_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible finite_intersection
/-- Exact finite-frame value of the actual second global coordinate. -/
@[expose] def q1_finite := ClutchedCoordinateFrames318.first_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible
  transition_unit infinity_intersection
/-- Exact infinity-frame value of the actual second global coordinate. -/
@[expose] def q1_infinity := ClutchedCoordinateFrames318.second_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible finite_intersection
end ProjectiveLineCoordinateFrames318
