module
public import PELOriginalInvariantMapOpenDescent318
public import InvariantMorphismSectionPullback318
public section
noncomputable section
namespace PELOriginalLocalTargetRingMaps318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalInvariantMapOpenDescent318 PELOriginalDeckFixedSections318
variable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
  (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens)

/-- Actual pullback from the arbitrary target's open V to the FULL
preimage of its produced descended domain open, with no hand-chosen iso. -/
@[expose] def targetSectionPullback:
    Γ(Z,V)→+*Γ(Model,morphism i⁻¹ᵁ(descendedOpen i g hg V)):=
  (g.appLE V _ (preimage_descendedOpen i g hg V).le).hom

lemma targetSectionPullback_fixed (r:Γ(Z,V)):
    DeckFixed i (descendedOpen i g hg V) (targetSectionPullback i g hg V r):=by
  intro a ha
  exact congrArg (fun k:Γ(Z,V)⟶Γ(Model,morphism i⁻¹ᵁ(descendedOpen i g hg V))=>k r)
    (InvariantMorphismSectionPullback318.appLE_fixed (schemeDeck a) g (hg ⟨a,ha⟩)
      V _ (preimage_descendedOpen i g hg V).le
        (preimage_stable i (descendedOpen i g hg V) a ha).ge)

/-- Actual UNIQUE descended section-ring map on each produced domain
open for an invariant map into an arbitrary scheme. -/
theorem existsUnique_targetRingMap:
    ∃!k:Γ(Z,V)→+*Γ(Curve i,descendedOpen i g hg V),
      ((morphism i).app (descendedOpen i g hg V)).hom.comp k=
        targetSectionPullback i g hg V:=
  PELOriginalDeckSectionDescent318.existsUnique_factor i _ _
    (targetSectionPullback_fixed i g hg V)

@[expose] def targetRingMap:Γ(Z,V)→+*Γ(Curve i,descendedOpen i g hg V):=
  Classical.choose (existsUnique_targetRingMap i g hg V)
lemma targetRingMap_square:
    ((morphism i).app (descendedOpen i g hg V)).hom.comp (targetRingMap i g hg V)=
      targetSectionPullback i g hg V:=
  (Classical.choose_spec (existsUnique_targetRingMap i g hg V)).1
lemma targetRingMap_unique (k:Γ(Z,V)→+*Γ(Curve i,descendedOpen i g hg V))
    (hk:((morphism i).app (descendedOpen i g hg V)).hom.comp k=
      targetSectionPullback i g hg V):k=targetRingMap i g hg V:=
  (Classical.choose_spec (existsUnique_targetRingMap i g hg V)).2 k hk
end PELOriginalLocalTargetRingMaps318
