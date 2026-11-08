module
public import FifthQuarticCompatibility318
public import FifthSourceAffine318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace FifthQuarticCompletedMap318
open AlgebraicGeometry CategoryTheory
open FifthQuarticCover318 FifthQuarticCompatibility318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 650000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Actual whole quartic affine map, including the original t=y=0 branch. -/
@[expose] def map:Spec (CommRingCat.of Quartic)⟶FifthCharacterShortScheme318.completed:=
  cover.glueMorphisms localMap compatible
@[reassoc] theorem restriction (b:Bool):cover.f b≫map=localMap b:=
  cover.ι_glueMorphisms localMap compatible b
@[reassoc] theorem on_branch:FifthBranchScheme318.inclusion≫map=FifthBranchScheme318.intoCompleted:=
  restriction true
@[reassoc] theorem branch_zero:FifthBranchScheme318.branch≫map=FifthCharacterShortScheme318.zero:=by
  rw [←FifthBranchScheme318.branchLift_inclusion,Category.assoc,on_branch,FifthBranchScheme318.branch_zero]
@[reassoc] theorem over_Q:map≫WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ Quartic)):=by
  apply cover.hom_ext
  intro b
  rw [←Category.assoc,restriction]
  cases b
  · rw [show localMap false=FifthQuarticFinite318.map from rfl,FifthQuarticFinite318.over_Q]
    change Spec.map (CommRingCat.ofHom (algebraMap ℚ FifthQuarticFinite318.Local))=
      Spec.map (CommRingCat.ofHom (algebraMap Quartic FifthQuarticFinite318.Local))≫_
    rw [←Spec.map_comp]
    congr 1
  · rw [show localMap true=FifthBranchScheme318.intoCompleted from rfl,FifthBranchScheme318.over_Q]
    change Spec.map (CommRingCat.ofHom (algebraMap ℚ FifthBranchLocal318.Local))=
      Spec.map (CommRingCat.ofHom (algebraMap Quartic FifthBranchLocal318.Local))≫_
    rw [←Spec.map_comp]
    congr 1
/-- Actual map from the entire original finite source chart to the fifth
completed short curve, not merely a rational character-field map. -/
@[expose] def sourceMap:Spec (CommRingCat.of FifthCharacterSource318.Source)⟶
    FifthCharacterShortScheme318.completed:=FifthSourceAffine318.map≫map
@[reassoc] theorem source_over_Q:sourceMap≫WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ FifthCharacterSource318.Source)):=by
  rw [sourceMap,Category.assoc,over_Q,FifthSourceAffine318.over_Q]
end FifthQuarticCompletedMap318
