module
public import FifthBranchLocal318
public import FifthCharacterShortScheme318
import all WeierstrassGluing318
public section
noncomputable section
namespace FifthBranchScheme318
open AlgebraicGeometry CategoryTheory
open FifthCharacterShortPolynomial318 FifthBranchLocal318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def neighborhood : Scheme:=Spec (CommRingCat.of Local)
@[expose] def quartic : Scheme:=Spec (CommRingCat.of Quartic)
@[expose] def inclusion : neighborhood ⟶ quartic:=
  Spec.map (CommRingCat.ofHom (algebraMap Quartic Local))
instance inclusion_open : IsOpenImmersion inclusion:=
  IsOpenImmersion.of_isLocalization denominator
@[expose] def intoCompleted : neighborhood ⟶ FifthCharacterShortScheme318.completed:=
  Spec.map (CommRingCat.ofHom infinityMap.toRingHom) ≫ WeierstrassGluing318.infinityChart A B
@[expose] def base : neighborhood ⟶ Spec (CommRingCat.of ℚ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Local))
@[reassoc] theorem over_Q : intoCompleted ≫ WeierstrassGluing318.structureMap A B=base:=by
  rw [intoCompleted,Category.assoc,WeierstrassGluing318.infinityChart_structure]
  change Spec.map (CommRingCat.ofHom infinityMap.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact infinityMap.commutes q
@[expose] def branch : Spec (CommRingCat.of ℚ) ⟶ quartic:=
  Spec.map (CommRingCat.ofHom origin.toRingHom)
@[expose] def branchLift : Spec (CommRingCat.of ℚ) ⟶ neighborhood:=
  Spec.map (CommRingCat.ofHom atOrigin.toRingHom)
@[reassoc] theorem branchLift_inclusion : branchLift ≫ inclusion=branch:=by
  rw [branchLift,inclusion,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact atOrigin_on_quartic
/-- Exact original branch point maps to the actual chosen elliptic zero. -/
@[reassoc] theorem branch_zero : branchLift ≫ intoCompleted=FifthCharacterShortScheme318.zero:=by
  rw [intoCompleted,←Category.assoc,branchLift,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (atOrigin.comp infinityMap).toRingHom) ≫ _=_
  rw [origin_composition]
  rfl
end FifthBranchScheme318
