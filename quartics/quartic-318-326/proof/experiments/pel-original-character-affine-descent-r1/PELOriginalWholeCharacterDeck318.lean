module
public import PELOriginalWholeCharacterFinite318
public section
noncomputable section
namespace PELOriginalWholeCharacterDeck318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalWholeCharacterOrders318 PELOriginalActualCharacterFields318
open PELOriginalCharacterQuotient318 PELOriginalMaximalQuotient318 OriginalContactInertiaBasis318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport the already proved exact whole-cubic kernel through the
OLD ordered affine coordinate equivalence, in both directions. -/
lemma ordered_ring_kernel (i:Fin 4) (g:Labels):
    (FourRootCoordinateRingSigns318.finiteEnd branches (basis g)).comp
      (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i)=
      PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i ↔ g∈(character i).ker:=by
  rw [←PELOriginalWholeCharacterOrders318.original_ring_kernel i g]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    have hx:=AlgHom.congr_fun h (PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i x)
    simpa only [PELOriginalOrderedCharacterSchemeMaps318.mapOnRings,AlgHom.comp_apply,
      AlgEquiv.coe_algHom,AlgEquiv.symm_apply_apply] using hx
  · intro h
    apply AlgHom.ext
    intro x
    exact AlgHom.congr_fun h ((PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv i).symm x)

lemma finite_deck_square (i:Fin 4) (g:Labels) (hg:g∈(character i).ker):
    FourRootSchemeSignAction318.finiteMap branches (basis g)≫finiteMap i=finiteMap i:=by
  have he:FourRootSchemeSignAction318.finiteMap branches (basis g)≫
      PELOriginalOrderedCharacterSchemeMaps318.morphism i=
      PELOriginalOrderedCharacterSchemeMaps318.morphism i:=by
    unfold FourRootSchemeSignAction318.finiteMap PELOriginalOrderedCharacterSchemeMaps318.morphism
    rw [←Spec.map_comp]
    exact congrArg (fun f=>Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
      ((ordered_ring_kernel i g).mpr hg)
  rw [finiteMap,←Category.assoc,he]

/-- Whole-source invariance under the exact original analytic character
kernel. Equality extends schematically from the unchanged finite chart,
with the original source action and complex structure square. -/
theorem whole_deck_square (i:Fin 4) (g:Labels) (hg:g∈(character i).ker):
    FourRootSchemeSignAction318.action branches (basis g)≫
      PELOriginalWholeCharacterMorphisms318.morphism i=
        PELOriginalWholeCharacterMorphisms318.morphism i:=by
  letI:=NormalizedLegendreProjectiveModel318.separated
    (PELOriginalOrderedCharacterCoordinate318.parameter i)
  apply FourRootSchematicDensity318.ext branches branches_injective
    (NormalizedLegendreProjectiveModel318.structure (PELOriginalOrderedCharacterCoordinate318.parameter i))
  · rw [Category.assoc,PELOriginalWholeCharacterMorphisms318.over_complex,
      FourRootSchemeSignAction318.over_base]
  · rw [←Category.assoc,FourRootSchemeSignAction318.finite_action,Category.assoc,
      PELOriginalWholeCharacterMorphisms318.on_finite,PELOriginalWholeCharacterMorphisms318.on_finite]
    exact finite_deck_square i g hg

/-- Conversely, fixing the global map forces membership in that same
original kernel. Restrict to the exact finite chart and cancel the MONO
target open immersion before using Spec faithfulness and the old ring kernel. -/
theorem whole_deck_iff (i:Fin 4) (g:Labels):
    FourRootSchemeSignAction318.action branches (basis g)≫
      PELOriginalWholeCharacterMorphisms318.morphism i=
        PELOriginalWholeCharacterMorphisms318.morphism i ↔ g∈(character i).ker:=by
  constructor
  · intro h
    have hf:=congrArg (fun f=>FourRootGluedScheme318.finiteChart branches≫f) h
    rw [←Category.assoc,FourRootSchemeSignAction318.finite_action,Category.assoc,
      PELOriginalWholeCharacterMorphisms318.on_finite,PELOriginalWholeCharacterMorphisms318.on_finite] at hf
    unfold finiteMap at hf
    rw [←Category.assoc] at hf
    have hm:FourRootSchemeSignAction318.finiteMap branches (basis g)≫
        PELOriginalOrderedCharacterSchemeMaps318.morphism i=
        PELOriginalOrderedCharacterSchemeMaps318.morphism i:=
      (cancel_mono (WeierstrassGluing318.finiteChart
        (PELOriginalOrderedCharacterCoordinates318.A i) (PELOriginalOrderedCharacterCoordinates318.B i))).mp hf
    unfold FourRootSchemeSignAction318.finiteMap PELOriginalOrderedCharacterSchemeMaps318.morphism at hm
    rw [←Spec.map_comp] at hm
    apply (ordered_ring_kernel i g).mp
    apply AlgHom.ext
    intro x
    have he:=Spec.map_injective hm
    exact congrArg (fun f=>f.hom x) he
  · exact whole_deck_square i g
end PELOriginalWholeCharacterDeck318
