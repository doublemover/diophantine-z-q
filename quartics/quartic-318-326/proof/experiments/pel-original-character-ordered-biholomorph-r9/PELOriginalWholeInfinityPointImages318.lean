module
public import PELOriginalDescendedCharacterKernel318
public section
noncomputable section
namespace PELOriginalWholeInfinityPointImages318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalMaximalQuotient318 PELOriginalKernelStableOpens318
open PELOriginalCharacterPullback318 OriginalContactInertiaBasis318

abbrev InfinityRing:=FourRootInfinityCoordinateRing318.Ring branches
@[expose] def infinityPoint (f:InfinityRing→ₐ[ℂ]ℂ):Spec (CommRingCat.of ℂ)⟶Model:=
  Spec.map (CommRingCat.ofHom f.toRingHom)≫FourRootGluedScheme318.infinityChart branches
@[expose] def origin (i:Fin 4):Spec (CommRingCat.of ℂ)⟶Curve i:=
  Spec.map (CommRingCat.ofHom (InfinityChart318.origin
    (PELOriginalOrderedCharacterCoordinates318.A i)
    (PELOriginalOrderedCharacterCoordinates318.B i)).toRingHom)≫
      WeierstrassGluing318.infinityChart
        (PELOriginalOrderedCharacterCoordinates318.A i)
        (PELOriginalOrderedCharacterCoordinates318.B i)

/-- Remove the auxiliary principal localization from the old infinity
point formula. This is the SAME actual morphism on the original chart. -/
lemma infinity_image (i:Fin 4) (f:InfinityRing→ₐ[ℂ]ℂ)
    (hu:f (FourRootInfinityCoordinateRing318.coordinate branches none)=0):
    infinityPoint f≫morphism i=origin i:=by
  let k:=PELOriginalCharacterInfinityMaps318.indices i
  have h:Spec.map (CommRingCat.ofHom
      (FourRootCharacterInfinityOpen318.pointLift branches k f hu).toRingHom)≫
      FourRootCharacterInfinityOpen318.inclusion branches k=
      Spec.map (CommRingCat.ofHom f.toRingHom):=by
    unfold FourRootCharacterInfinityOpen318.inclusion
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact FourRootCharacterInfinityOpen318.pointLift_on_ring branches k f hu x
  have he:=PELOriginalWholeCharacterMorphisms318.every_infinity_point i f hu
  change (Spec.map (CommRingCat.ofHom
      (FourRootCharacterInfinityOpen318.pointLift branches k f hu).toRingHom)≫
      (FourRootCharacterInfinityOpen318.inclusion branches k≫
        FourRootGluedScheme318.infinityChart branches))≫morphism i=origin i at he
  simpa only [←Category.assoc,h,infinityPoint] using he

/-- Scheme action on an original infinity point is the literal signed
ring precomposition, retaining the normalized s0=1 coordinate ring. -/
lemma infinity_point_action (f:InfinityRing→ₐ[ℂ]ℂ) (a:Labels):
    infinityPoint f≫schemeDeck a=
      infinityPoint (f.comp (FourRootCoordinateRingSigns318.infinityEnd branches (basis a))):=by
  unfold infinityPoint
  rw [Category.assoc,FourRootSchemeSignAction318.infinity_action,←Category.assoc]
  unfold FourRootSchemeSignAction318.infinityMap
  rw [←Spec.map_comp]
  rfl
lemma signed_infinity_zero (f:InfinityRing→ₐ[ℂ]ℂ) (a:Labels)
    (hu:f (FourRootInfinityCoordinateRing318.coordinate branches none)=0):
    (f.comp (FourRootCoordinateRingSigns318.infinityEnd branches (basis a)))
      (FourRootInfinityCoordinateRing318.coordinate branches none)=0:=by
  simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.infinity_parameter,
    map_mul,hu,mul_zero]

/-- An explicit original infinity point. No lifting of target points or
closed-point surjectivity is assumed in the fixed-origin argument. -/
@[expose] def unitInfinity:InfinityRing→ₐ[ℂ]ℂ:=
  FourRootInfinityCoordinateRing318.lift branches 0 (fun _=>1) rfl (by intro k;simp)
lemma unitInfinity_zero:unitInfinity (FourRootInfinityCoordinateRing318.coordinate branches none)=0:=by
  exact FourRootInfinityCoordinateRing318.lift_coordinate branches 0 (fun _=>1) rfl
    (by intro k;simp) none
end PELOriginalWholeInfinityPointImages318
