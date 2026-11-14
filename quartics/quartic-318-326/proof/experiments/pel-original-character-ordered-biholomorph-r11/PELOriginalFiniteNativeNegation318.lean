module
public import PELOriginalFiniteCharacterSigns318
public import GluedNegation318
public section
noncomputable section
namespace PELOriginalFiniteNativeNegation318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterSchemeMaps318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalFiniteCharacterSigns318

/-- The actual ordered affine coordinate map intertwines the ORIGINAL
toggle and the native (x,y) to (x,-y) ring map. Not merely equal kernels. -/
lemma exact_ring_square (i:Fin 4):
    (FourRootCoordinateRingSigns318.finiteEnd branches (basis (toggle i))).comp
      (mapOnRings i)=
    (mapOnRings i).comp (ChartNegation318.affineNeg (A i) (B i)):=by
  apply WeierstrassOverlap318.affine_hom_ext
  · simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_x] using
      signed_x i (toggle i)
  · simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using toggle_y i

lemma exact_affine_square (i:Fin 4):
    FourRootSchemeSignAction318.finiteMap branches (basis (toggle i))≫
      PELOriginalOrderedCharacterSchemeMaps318.morphism i=
    PELOriginalOrderedCharacterSchemeMaps318.morphism i≫GluedNegation318.finiteNeg (A i) (B i):=by
  unfold FourRootSchemeSignAction318.finiteMap
    PELOriginalOrderedCharacterSchemeMaps318.morphism GluedNegation318.finiteNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (exact_ring_square i)

/-- Equality on the entire finite contact chart, with the SAME target
chart inclusion as in the global quotient construction. -/
lemma finite_native_square (i:Fin 4):
    FourRootSchemeSignAction318.finiteMap branches (basis (toggle i))≫finiteMap i=
      finiteMap i≫GluedNegation318.negation (A i) (B i):=by
  rw [finiteMap,←Category.assoc,exact_affine_square,Category.assoc,
    ←GluedNegation318.finiteChart_negation,←Category.assoc]
end PELOriginalFiniteNativeNegation318
