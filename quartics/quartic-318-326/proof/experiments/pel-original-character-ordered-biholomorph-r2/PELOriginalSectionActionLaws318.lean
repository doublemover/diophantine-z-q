module
public import StableOpenSectionLaws318
public import PELOriginalAffineTargetSchemeDescent318
public section
noncomputable section
namespace PELOriginalSectionActionLaws318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalKernelStableOpens318 StableOpenSectionPullback318 StableOpenSectionLaws318

lemma schemeDeck_mul (a b:Labels):schemeDeck (a*b)=schemeDeck a≫schemeDeck b:=by
  change FourRootSchemeSignAction318.action branches (basis (a*b))=_
  rw [map_mul,FourRootSchemeSignAction318.action_mul]
lemma schemeDeck_one:schemeDeck (1:Labels)=𝟙 Model:=by
  change FourRootSchemeSignAction318.action branches (basis 1)=_
  rw [map_one,FourRootSchemeSignAction318.action_one]

lemma sectionAction_mul (i:Fin 4) (U:(Curve i).Opens)
    (a b:Labels) (ha:a∈(character i).ker) (hb:b∈(character i).ker)
    (hab:a*b∈(character i).ker):
    sectionAction i U (a*b) hab=
      (sectionAction i U a ha).comp (sectionAction i U b hb):=by
  let V:=morphism i⁻¹ᵁU
  have hf:V≤(schemeDeck a≫schemeDeck b)⁻¹ᵁV:=
    (preimage_stable i U a ha).ge.trans
      ((schemeDeck a).preimage_mono (preimage_stable i U b hb).ge)
  exact (sectionPullback_congr (schemeDeck_mul a b) V
    (preimage_stable i U (a*b) hab).ge hf).trans
      (sectionPullback_comp (schemeDeck a) (schemeDeck b) V _ _ hf)

lemma sectionAction_one (i:Fin 4) (U:(Curve i).Opens)
    (h:(1:Labels)∈(character i).ker):
    sectionAction i U 1 h=RingHom.id Γ(Model,morphism i⁻¹ᵁU):=by
  exact (sectionPullback_congr schemeDeck_one _
    (preimage_stable i U 1 h).ge le_rfl).trans (sectionPullback_id _ le_rfl)
end PELOriginalSectionActionLaws318
