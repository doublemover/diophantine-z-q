module
public import PELOriginalResidualProjectionScheme318
public import FourRootSchemePointEquivariance318
public section
noncomputable section
namespace PELOriginalOrderedCharacterPointMap318
open AlgebraicGeometry CategoryTheory
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCharacterQuotient318 PELOriginalWholeCharacterMorphisms318
open PELOriginalOrderedCharacterCoordinates318 PELOriginalKernelStableOpens318

abbrev Points (i:Fin 4):=CompletedFieldPoints318.SchemePoints (K:=ℂ) (A i) (B i)
/-- Literal composition of the already constructed WHOLE original source
comparison and actual ordered finite-flat Scheme map. No root is re-chosen. -/
@[expose] def sourceMap (i:Fin 4) (x:UnlevelledBase):Points i:=
  ⟨(PELOriginalContactSchemePoints318.comparison x).val≫morphism i,by
    rw [Category.assoc,over_complex]
    exact (PELOriginalContactSchemePoints318.comparison x).property⟩

lemma source_equivariant (i:Fin 4) (a:PELOriginalMaximalQuotient318.Labels)
    (x:UnlevelledBase):
    (sourceMap i (a • x)).val=(PELOriginalContactSchemePoints318.comparison x).val≫
      schemeDeck a≫morphism i:=by
  change (PELOriginalContactSchemePoints318.comparison (a • x)).val≫morphism i=_
  rw [FourRootSchemePointEquivariance318.original_equivariant]
  exact Category.assoc _ _ _

lemma kernel_invariant (i:Fin 4) (a:(character i).ker) (x:UnlevelledBase):
    sourceMap i ((a:PELOriginalMaximalQuotient318.Labels) • x)=sourceMap i x:=by
  apply Subtype.ext
  rw [source_equivariant,PELOriginalWholeCharacterDeck318.whole_deck_square i a.val a.property]
  rfl

/-- Descent through the ORIGINAL analytic orbit quotient to the actual
ordered algebraic Scheme-valued points. Its source is not a new quotient. -/
@[expose] def pointMap (i:Fin 4):CharacterBase i→Points i:=
  Quotient.lift (sourceMap i) (by
    intro x y h
    obtain ⟨a,ha⟩:=h
    rw [←ha]
    exact kernel_invariant i a y)
lemma on_source (i:Fin 4) (x:UnlevelledBase):pointMap i (toCharacter i x)=sourceMap i x:=rfl
end PELOriginalOrderedCharacterPointMap318
