module
public import PELOriginalCharacterRefinedCover318
public import CompletedCharacterGlobal318
public section
noncomputable section
namespace PELOriginalWholeCharacterMorphisms318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalCharacterRefinedCover318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Curve (i:Fin 4):=NormalizedLegendreProjectiveModel318.model
  (PELOriginalOrderedCharacterCoordinate318.parameter i)
@[expose] def finiteMap (i:Fin 4):FourRootGluedScheme318.finiteScheme branches⟶Curve i:=
  PELOriginalOrderedCharacterSchemeMaps318.morphism i≫WeierstrassGluing318.finiteChart (A i) (B i)
@[expose] def infinityMap (i:Fin 4):Spec (CommRingCat.of (PELOriginalCharacterActualOverlap318.N i))⟶Curve i:=
  PELOriginalCharacterInfinityMaps318.morphism i

lemma maps_agree (i:Fin 4):intoFinite i≫finiteMap i=intoInfinity i≫infinityMap i:=by
  unfold intoFinite intoInfinity finiteMap infinityMap
    PELOriginalOrderedCharacterSchemeMaps318.morphism PELOriginalCharacterInfinityMaps318.morphism
  rw [←Category.assoc,←Spec.map_comp,←Category.assoc,←Spec.map_comp]
  exact PELOriginalCharacterActualOverlap318.target_scheme_square i

@[expose] def localMap (i:Fin 4):(b:Bool)→(cover i).X b⟶Curve i
  | false=>finiteMap i
  | true=>infinityMap i
lemma compatible (i:Fin 4) (b d:Bool):
    pullback.fst ((cover i).f b) ((cover i).f d)≫localMap i b=
      pullback.snd _ _≫localMap i d:=by
  cases b <;> cases d
  · exact CompletedCharacterGlobal318.diagonal_compatibility
      (FourRootGluedScheme318.finiteChart branches) (finiteMap i)
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback (actual_pullback i)
      (finiteMap i) (infinityMap i) (maps_agree i)
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback (actual_pullback i).flip
      (infinityMap i) (finiteMap i) (maps_agree i).symm
  · exact CompletedCharacterGlobal318.diagonal_compatibility (infinityChart i) (infinityMap i)

/-- Actual morphisms from the WHOLE original independently glued contact
scheme to the same ordered independent Legendre models. This is not an
isomorphism between the genus-five source and its elliptic targets. -/
@[expose] def morphism (i:Fin 4):FourRootGluedScheme318.scheme branches⟶Curve i:=
  (cover i).glueMorphisms (localMap i) (compatible i)
lemma on_finite (i:Fin 4):FourRootGluedScheme318.finiteChart branches≫morphism i=finiteMap i:=
  (cover i).ι_glueMorphisms (localMap i) (compatible i) false
lemma on_infinity (i:Fin 4):infinityChart i≫morphism i=infinityMap i:=
  (cover i).ι_glueMorphisms (localMap i) (compatible i) true

lemma infinity_structure (i:Fin 4):infinityChart i≫FourRootGluedScheme318.structureMap branches=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (PELOriginalCharacterActualOverlap318.N i))):=by
  rw [infinityChart,Category.assoc,FourRootGluedScheme318.infinity_structure]
  unfold FourRootCharacterInfinityOpen318.inclusion FourRootGluedScheme318.infinityBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (IsScalarTower.algebraMap_apply ℂ PELOriginalCharacterActualOverlap318.I
    (PELOriginalCharacterActualOverlap318.N i) z).symm

/-- The structure square uses the original complex structures on both
schemes, not a transported or arbitrary algebra action. -/
theorem over_complex (i:Fin 4):morphism i≫WeierstrassGluing318.structureMap (A i) (B i)=
    FourRootGluedScheme318.structureMap branches:=by
  apply (cover i).hom_ext
  intro b
  cases b
  · change FourRootGluedScheme318.finiteChart branches≫morphism i≫_=_
    rw [←Category.assoc,on_finite,finiteMap,Category.assoc,
      WeierstrassGluing318.finiteChart_structure,PELOriginalOrderedCharacterSchemeMaps318.over_complex,
      FourRootGluedScheme318.finite_structure]
  · change infinityChart i≫morphism i≫_=_
    rw [←Category.assoc,on_infinity,infinityMap,
      PELOriginalCharacterInfinityMaps318.over_complex,infinity_structure]

theorem unique (i:Fin 4) (f:FourRootGluedScheme318.scheme branches⟶Curve i)
    (hf:FourRootGluedScheme318.finiteChart branches≫f=finiteMap i)
    (hi:infinityChart i≫f=infinityMap i):f=morphism i:=by
  apply (cover i).hom_ext
  intro b
  cases b
  · exact hf.trans (on_finite i).symm
  · exact hi.trans (on_infinity i).symm

/-- Every old point above infinity maps to the actual elliptic origin.
The source retains its eight points; they are not identified in the source. -/
theorem every_infinity_point (i:Fin 4)
    (f:FourRootInfinityCoordinateRing318.Ring branches→ₐ[ℂ]ℂ)
    (hu:f (FourRootInfinityCoordinateRing318.coordinate branches none)=0):
    Spec.map (CommRingCat.ofHom (FourRootCharacterInfinityOpen318.pointLift branches
      (PELOriginalCharacterInfinityMaps318.indices i) f hu).toRingHom)≫
      infinityChart i≫morphism i=
    Spec.map (CommRingCat.ofHom (InfinityChart318.origin (A i) (B i)).toRingHom)≫
      WeierstrassGluing318.infinityChart (A i) (B i):=by
  rw [on_infinity]
  exact PELOriginalCharacterInfinityMaps318.point_scheme_square i f hu
end PELOriginalWholeCharacterMorphisms318
