module
public import CharacterSignAffine318
public import CompletedCharacterGlobal318
public import CompletedCharacterProper318
public import SchematicEqualityExtension318
public import GluedNegation318
public section
noncomputable section
namespace CharacterSignGlobal318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def affineMap (i:Fin 4):ContactKummerCover318.cover units⟶
    ShortAffineScheme318.scheme (publishedA i) (publishedB i):=
  Spec.map (CommRingCat.ofHom (CharacterSignAffine318.openPublished i).toRingHom)
lemma source_affine (i:Fin 4):ContactOverlapMaps318.sourceInclusion units≫
    SourceCharacterAffine318.publishedMap i=affineMap i:=by
  unfold ContactOverlapMaps318.sourceInclusion SourceCharacterAffine318.publishedMap affineMap
  rw [←Spec.map_comp]
  rfl
lemma on_open (i:Fin 4):ContactProjectiveModel318.sourceOpen units≫completedMap i=
    affineMap i≫WeierstrassGluing318.finiteChart (publishedA i) (publishedB i):=by
  rw [←ContactOverlapMaps318.source_square,Category.assoc,CompletedCharacterGlobal318.on_finite,
    finiteChartMap,←Category.assoc,source_affine]
lemma open_omitted (i:Fin 4):
    ContactGlobalSigns318.openMap units (SourceCharacterFields318.flip i)≫affineMap i=affineMap i:=by
  unfold ContactGlobalSigns318.openMap affineMap
  rw [←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (CharacterSignAffine318.omitted_affine i))
lemma open_other (i j:Fin 4) (hji:j≠i):
    ContactGlobalSigns318.openMap units (SourceCharacterFields318.flip j)≫affineMap i=
      affineMap i≫GluedNegation318.finiteNeg (publishedA i) (publishedB i):=by
  unfold ContactGlobalSigns318.openMap affineMap GluedNegation318.finiteNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (CharacterSignAffine318.other_affine i j hji))

local instance sourceIntegral:IsIntegral (ContactProjectiveModel318.model units):=
  (ContactGlobalProper318.proper_integral_extension units).2.1
local instance sourceOpenDominant:IsDominant (ContactProjectiveModel318.sourceOpen units):=
  ContactProjectiveModel318.sourceOpen_dense units
local instance sourceOpenDense:IsSchemeTheoreticallyDominant (ContactProjectiveModel318.sourceOpen units):=
  IsSchemeTheoreticallyDominant.of_isDominant (ContactProjectiveModel318.sourceOpen units)

lemma source_ext (i:Fin 4) (f g:ContactProjectiveModel318.model units⟶Target i)
    (hb:f≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=
      g≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
    (ho:ContactProjectiveModel318.sourceOpen units≫f=ContactProjectiveModel318.sourceOpen units≫g):f=g:=by
  letI:=CubicClosedImmersion318.structure_separated (publishedA i) (publishedB i)
  exact SchematicEqualityExtension318.ext _ hb (ContactProjectiveModel318.sourceOpen units) ho

lemma signed_over_Q (i:Fin 4) (b:Fin 4→Bool):
    (ContactGlobalSigns318.map units b≫completedMap i)≫
      WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=
      completedMap i≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i):=by
  rw [Category.assoc,over_Q]
  change ContactGlobalSigns318.map units b≫ContactProjectiveModel318.modelMap units≫
    ProjectiveJLine318.structureMap ℚ=_
  rw [←Category.assoc,ContactGlobalSigns318.over_line]
  rfl

/-- The omitted root flip fixes the actual entire completed quotient map. -/
theorem omitted (i:Fin 4):
    ContactGlobalSigns318.map units (SourceCharacterFields318.flip i)≫completedMap i=completedMap i:=by
  apply source_ext i _ _ (signed_over_Q i _)
  rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,
    ←Category.assoc,open_omitted]

/-- Every other source-root flip descends to the actual global elliptic
involution, on all points including the ramification and infinity loci. -/
theorem other (i j:Fin 4) (hji:j≠i):
    ContactGlobalSigns318.map units (SourceCharacterFields318.flip j)≫completedMap i=
      completedMap i≫GluedNegation318.negation (publishedA i) (publishedB i):=by
  apply source_ext i
  · simpa only [Category.assoc,GluedNegation318.negation_over_base] using
      (signed_over_Q i (SourceCharacterFields318.flip j))
  · rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,
      ←Category.assoc,open_other i j hji,Category.assoc]
    rw [←Category.assoc (ContactProjectiveModel318.sourceOpen units) (completedMap i),on_open]
    simp only [Category.assoc,GluedNegation318.finiteChart_negation]
end CharacterSignGlobal318
