module
public import PELOriginalSectionKernelAction318
public section
noncomputable section
namespace PELOriginalSectionInvariantExtension318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalDeckFixedSections318
open PELOriginalSectionKernelAction318

/-- Base sections are fixed by the ACTUAL action, since their original
whole-map pullbacks are precisely in the already proved fixed image. -/
lemma base_fixed (i:Fin 4) (U:(Curve i).Opens) (a:Kernel i) (r:BaseSections i U):
    sectionAction i U a.val a.property ((morphism i).app U r)=
      (morphism i).app U r:=
  (PELOriginalDeckSectionDescent318.range_iff_fixed i U _).mp ⟨r,rfl⟩ a.val a.property

@[expose] def sectionScalarComm (i:Fin 4) (U:(Curve i).Opens):
    letI:=sectionActionInstance i U
    letI:=sectionAlgebra i U
    SMulCommClass (Kernel i) (BaseSections i U) (SourceSections i U):=by
  letI:=sectionActionInstance i U
  letI:=sectionAlgebra i U
  refine ⟨?_⟩
  intro a r x
  change sectionAction i U a.val a.property (((morphism i).app U r)*x)=
    ((morphism i).app U r)*(sectionAction i U a.val a.property x)
  rw [map_mul,base_fixed]

/-- Native IsInvariant is PRODUCED from the actual all-open image
criterion. It is not a new fixed-ring hypothesis supplied by the caller. -/
@[expose] def sectionIsInvariant (i:Fin 4) (U:(Curve i).Opens):
    letI:=sectionActionInstance i U
    letI:=sectionAlgebra i U
    Algebra.IsInvariant (BaseSections i U) (SourceSections i U) (Kernel i):=by
  letI:=sectionActionInstance i U
  letI:=sectionAlgebra i U
  constructor
  intro x hx
  apply (PELOriginalDeckSectionDescent318.range_iff_fixed i U x).mpr
  intro a ha
  exact hx ⟨a,ha⟩
end PELOriginalSectionInvariantExtension318
