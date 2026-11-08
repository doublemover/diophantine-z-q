module
public import GeometricFibers318
public import CubicClosedImmersion318
public import CompletedAdditionTriple318
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace RationalProductReduced318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (A B:ℚ)
local notation "p"=>WeierstrassGluing318.structureMap A B
local instance : IsProper p:=CubicClosedImmersion318.structure_proper A B
lemma curve_reduced : IsReduced (WeierstrassGluing318.scheme A B):=by
  haveI:=CompletedIntegral318.completed_integral A B
  infer_instance
lemma curve_noetherian : IsLocallyNoetherian (WeierstrassGluing318.scheme A B):=
  LocallyOfFiniteType.isLocallyNoetherian p
lemma pair_reduced : IsReduced (pullback p p):=by
  haveI:=curve_reduced A B
  haveI:=curve_noetherian A B
  haveI:=GeometricFibers318.geometrically_integral A B
  infer_instance
lemma pair_noetherian : IsLocallyNoetherian (pullback p p):=by
  haveI:=curve_noetherian A B
  infer_instance
/-- The exact left-associated relative triple is reduced over Q. This
field-specific equality bridge is not asserted over nilpotent bases. -/
theorem triple_reduced : IsReduced (CompletedAdditionTriple318.triple A B):=by
  haveI:=pair_reduced A B
  haveI:=pair_noetherian A B
  haveI:=GeometricFibers318.geometrically_integral A B
  change IsReduced (pullback (pullback.fst p p ≫ p) p)
  infer_instance
end RationalProductReduced318
