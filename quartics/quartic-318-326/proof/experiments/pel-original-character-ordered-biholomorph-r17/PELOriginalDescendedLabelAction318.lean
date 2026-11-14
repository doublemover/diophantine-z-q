module
public import PELOriginalDescendedLabelMaps318
public section
noncomputable section
namespace PELOriginalDescendedLabelAction318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318 PELOriginalMaximalQuotient318
open PELOriginalKernelStableOpens318 PELOriginalSectionActionLaws318
open PELOriginalDescendedLabelMaps318 OriginalContactInertiaBasis318

lemma descended_one (i:Fin 4):descended i (1:Labels)=𝟙 (Curve i):=by
  apply cancel_original i
  rw [descended_square,schemeDeck_one,Category.id_comp,Category.comp_id]
lemma descended_mul (i:Fin 4) (a b:Labels):
    descended i (a*b)=descended i a≫descended i b:=by
  apply cancel_original i
  rw [descended_square,schemeDeck_mul,Category.assoc,←descended_square,
    ←Category.assoc,descended_square]
lemma descended_square_id (i:Fin 4) (a:Labels):
    descended i a≫descended i a=𝟙 (Curve i):=by
  apply cancel_original i
  rw [←Category.assoc,descended_square,Category.assoc,descended_square,
    ←Category.assoc,Category.comp_id]
  change (FourRootSchemeSignAction318.action branches (basis a)≫
    FourRootSchemeSignAction318.action branches (basis a))≫morphism i=morphism i
  rw [FourRootSchemeSignAction318.action_square,Category.id_comp]

/-- Actual scheme automorphism, with its inverse proved from the original
involutive source action rather than chosen from a point permutation. -/
@[expose] def descendedIso (i:Fin 4) (a:Labels):Curve i≅Curve i where
  hom:=descended i a
  inv:=descended i a
  hom_inv_id:=descended_square_id i a
  inv_hom_id:=descended_square_id i a

lemma descended_over_complex (i:Fin 4) (a:Labels):
    descended i a≫WeierstrassGluing318.structureMap
      (PELOriginalOrderedCharacterCoordinates318.A i)
      (PELOriginalOrderedCharacterCoordinates318.B i)=
    WeierstrassGluing318.structureMap
      (PELOriginalOrderedCharacterCoordinates318.A i)
      (PELOriginalOrderedCharacterCoordinates318.B i):=by
  apply cancel_original i
  rw [←Category.assoc,descended_square,Category.assoc,
    PELOriginalWholeCharacterMorphisms318.over_complex,
    PELOriginalWholeCharacterMorphisms318.over_complex]
  exact FourRootSchemeSignAction318.over_base branches (basis a)
end PELOriginalDescendedLabelAction318
