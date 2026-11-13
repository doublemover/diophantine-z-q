module
public import PELOriginalWholeSchemeQuotient318
public section
noncomputable section
namespace PELOriginalDescendedLabelMaps318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalSectionActionLaws318
local instance mapFlat (i:Fin 4):Flat (morphism i):=PELOriginalWholeCharacterFlat318.flat i
local instance mapSurjective (i:Fin 4):Surjective (morphism i):=PELOriginalWholeCharacterProper318.surjective i

lemma original_maps_commute (a b:Labels):schemeDeck a≫schemeDeck b=schemeDeck b≫schemeDeck a:=by
  rw [←schemeDeck_mul,←schemeDeck_mul,mul_comm]

lemma translate_invariant (i:Fin 4) (a:Labels) (k:Kernel i):
    schemeDeck k.val≫(schemeDeck a≫morphism i)=schemeDeck a≫morphism i:=by
  rw [←Category.assoc,original_maps_commute,Category.assoc,
    PELOriginalWholeCharacterDeck318.whole_deck_square i k.val k.property]

/-- Descend the SAME original label map, not an independently chosen
elliptic involution. Its defining square is a whole scheme equality. -/
@[expose] def descended (i:Fin 4) (a:Labels):Curve i⟶Curve i:=
  Classical.choose (PELOriginalWholeSchemeQuotient318.existsUnique_factor i
    (schemeDeck a≫morphism i) (translate_invariant i a))
lemma descended_square (i:Fin 4) (a:Labels):
    morphism i≫descended i a=schemeDeck a≫morphism i:=
  (Classical.choose_spec (PELOriginalWholeSchemeQuotient318.existsUnique_factor i
    (schemeDeck a≫morphism i) (translate_invariant i a))).1

/-- Cancellation is supplied by the actual flat-surjective original
map. It is not assumed as an extra property of a purported quotient. -/
lemma cancel_original {Z:Scheme} (i:Fin 4) {f g:Curve i⟶Z}
    (h:morphism i≫f=morphism i≫g):f=g:=by
  letI:Epi (morphism i):=Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (morphism i)).mp h

lemma descended_unique (i:Fin 4) (a:Labels) (f:Curve i⟶Curve i)
    (h:morphism i≫f=schemeDeck a≫morphism i):f=descended i a:=
  cancel_original i (h.trans (descended_square i a).symm)
end PELOriginalDescendedLabelMaps318
