module
public import IntegralProjectiveLineOverlap318
public import ClutchedModuleTop318
public section
noncomputable section
namespace IntegralProjectiveLineOOne318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralProjectiveLineOverlap318 ClutchedModule318 ClutchedModuleFrames318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]

/-- Independent target transition, over the entire integral projective
line overlap. The convention e0=t*e1 is O(1), not its inverse. -/
@[expose] def transition : Γ(Spec (CommRingCat.of (A R)),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A R))).inv (t R)
theorem transition_unit : IsUnit (transition R) := by
  have ht : IsUnit (t R) := tUnit_coe R ▸ (tUnit R).isUnit
  exact ht.map (Scheme.ΓSpecIso (CommRingCat.of (A R))).inv.hom

/-- O(1) is built on the target independently of the contact curve and its
sections, by actual two-chart unit-module gluing with transition t. -/
@[expose] def line : (ProjectiveJLine318.scheme R).Modules :=
  sheaf (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
    (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
@[expose] def finiteFrame : (line R).restrict (JLineAtlas318.chart R 1) ≅
    unit (Spec (CommRingCat.of R[X])) :=
  firstFrame (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
    (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
    (transition_unit R) (infinity_intersection R)
@[expose] def infinityFrame : (line R).restrict (JLineAtlas318.chart R 0) ≅
    unit (Spec (CommRingCat.of R[X])) :=
  secondFrame (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
    (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
    (finite_intersection R)
end IntegralProjectiveLineOOne318
