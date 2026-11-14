module
public import PELOriginalSectionActionLaws318
public import Mathlib.RingTheory.Invariant.Basic
public section
noncomputable section
namespace PELOriginalSectionKernelAction318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalSectionActionLaws318

abbrev Kernel (i:Fin 4):=↥(character i).ker
abbrev BaseSections (i:Fin 4) (U:(Curve i).Opens):=Γ(Curve i,U)
abbrev SourceSections (i:Fin 4) (U:(Curve i).Opens):=Γ(Model,morphism i⁻¹ᵁU)

/-- The finite original kernel acts on ACTUAL regular sections by the
original glued scheme pullbacks, with group laws proved by native appLE. -/
@[expose,instance_reducible] def sectionActionInstance (i:Fin 4) (U:(Curve i).Opens):
    MulSemiringAction (Kernel i) (SourceSections i U) where
  smul a x:=sectionAction i U a.val a.property x
  one_smul x:=RingHom.congr_fun (sectionAction_one i U (character i).ker.one_mem) x
  mul_smul a b x:=RingHom.congr_fun
    (sectionAction_mul i U a.val b.val a.property b.property (a*b).property) x
  smul_zero a:=(sectionAction i U a.val a.property).map_zero
  smul_add a x y:=(sectionAction i U a.val a.property).map_add x y
  smul_one a:=(sectionAction i U a.val a.property).map_one
  smul_mul a x y:=(sectionAction i U a.val a.property).map_mul x y

/-- The algebra is the SAME original whole morphism's section map. -/
@[expose,instance_reducible] def sectionAlgebra (i:Fin 4) (U:(Curve i).Opens):
    Algebra (BaseSections i U) (SourceSections i U):=((morphism i).app U).hom.toAlgebra
end PELOriginalSectionKernelAction318
