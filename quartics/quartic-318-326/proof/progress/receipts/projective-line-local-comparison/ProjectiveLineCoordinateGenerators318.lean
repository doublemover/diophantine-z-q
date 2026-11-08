module
public import ClutchedCoordinateGenerators318
public import ProjectiveLineCoordinateFrames318
public section
noncomputable section
namespace ProjectiveLineCoordinateGenerators318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ProjectiveLineOOne318 ProjectiveLineCoordinates318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- The actual first coordinate morphism freely generates on the entire finite chart. -/
@[expose] def zero_finite_isIso := ClutchedCoordinateGenerators318.first_isIso
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
  transition_unit infinity_intersection isUnit_one
/-- The actual second coordinate morphism freely generates on the entire infinity chart. -/
@[expose] def one_infinity_isIso := ClutchedCoordinateGenerators318.second_isIso
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible finite_intersection isUnit_one
end ProjectiveLineCoordinateGenerators318
