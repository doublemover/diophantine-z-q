module
public import PELOriginalCharacterInvariantRing318
public section
noncomputable section
namespace PELOriginalCharacterAffineQuotient318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalCharacterInvariantRing318
abbrev QuotientChart (i:Fin 4):Scheme:=Spec (CommRingCat.of (invariantSubring i))
@[expose] def quotientMap (i:Fin 4):FourRootGluedScheme318.finiteScheme branches⟶QuotientChart i:=
  Spec.map (CommRingCat.ofHom (invariantSubring i).subtype)

/-- The actual independent ordered target affine chart is isomorphic to
Spec of the literal invariant subring inside the old finite source. -/
@[expose] def targetIso (i:Fin 4):QuotientChart i≅ShortAffineScheme318.scheme (A i) (B i) where
  hom:=Spec.map (CommRingCat.ofHom (coordinateEquiv i).toRingHom)
  inv:=Spec.map (CommRingCat.ofHom (coordinateEquiv i).symm.toRingHom)
  hom_inv_id:=by
    rw [←Spec.map_comp]
    have h:(coordinateEquiv i).toRingHom.comp (coordinateEquiv i).symm.toRingHom=RingHom.id _:=by
      ext x
      exact (coordinateEquiv i).apply_symm_apply x
    change Spec.map (CommRingCat.ofHom
      ((coordinateEquiv i).toRingHom.comp (coordinateEquiv i).symm.toRingHom))=_
    rw [h]
    simp
  inv_hom_id:=by
    rw [←Spec.map_comp]
    have h:(coordinateEquiv i).symm.toRingHom.comp (coordinateEquiv i).toRingHom=RingHom.id _:=by
      ext x
      exact (coordinateEquiv i).symm_apply_apply x
    change Spec.map (CommRingCat.ofHom
      ((coordinateEquiv i).symm.toRingHom.comp (coordinateEquiv i).toRingHom))=_
    rw [h]
    simp

/-- The quotient coordinate map followed by this isomorphism is exactly
the old whole finite character morphism, not an abstract isomorphic map. -/
theorem actual_square (i:Fin 4):quotientMap i≫(targetIso i).hom=
    PELOriginalOrderedCharacterSchemeMaps318.morphism i:=by
  change Spec.map (CommRingCat.ofHom (invariantSubring i).subtype)≫
    Spec.map (CommRingCat.ofHom (coordinateEquiv i).toRingHom)=_
  rw [←Spec.map_comp]
  rfl

/-- Retain the same identity after inclusion in the global elliptic
target and restriction of the proved global degree-eight map. No global
categorical quotient universal property is asserted from this chart alone. -/
theorem whole_square (i:Fin 4):quotientMap i≫(targetIso i).hom≫
    WeierstrassGluing318.finiteChart (A i) (B i)=
      FourRootGluedScheme318.finiteChart branches≫PELOriginalWholeCharacterMorphisms318.morphism i:=by
  rw [←Category.assoc,actual_square,PELOriginalWholeCharacterMorphisms318.on_finite]
  rfl
end PELOriginalCharacterAffineQuotient318
