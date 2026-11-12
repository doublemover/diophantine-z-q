module
public import CocycleModule318
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public section
noncomputable section
namespace CocycleModuleCone318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
@[expose] def index : MulticospanIndex (MulticospanShape.prod ι) X.Modules where
  left := CocycleModule318.chart U
  right := fun ij=>CocycleModule318.overlap U ij.1 ij.2
  fst := fun ij=>CocycleModule318.left U ij.1 ij.2
  snd := fun ij=>CocycleModule318.right U c ij.1 ij.2
/-- The actual compatible-coefficient module, viewed as the original
full-overlap multicospan cone rather than an unrelated replacement object. -/
@[expose] def cone : Multifork (index U c) :=
  Multifork.ofι _ (CocycleModule318.object U c) (CocycleModule318.coefficient U c)
    (fun ij=>CocycleModule318.compatible U c ij.1 ij.2)
@[expose] def isLimit : IsLimit (cone U c) :=
  Multifork.IsLimit.mk _
    (fun E=>CocycleModule318.lift U c E.ι (fun i j=>E.condition (i,j)))
    (fun E i=>CocycleModule318.lift_coefficient U c E.ι
      (fun i j=>E.condition (i,j)) i)
    (fun E m hm=>CocycleModule318.hom_ext U c _ _ (fun i=>by
      rw [CocycleModule318.lift_coefficient]
      exact hm i))
/-- Open restriction preserves these arbitrary small coefficient diagrams;
no finiteness of the cover is imposed. -/
instance restrictionPreservesLimit {Y:Scheme.{u}} (j:Y⟶X) [IsOpenImmersion j]
    {J:Type u} [SmallCategory J] (F:J⥤X.Modules):
    PreservesLimit F (Scheme.Modules.restrictFunctor j) := by
  haveI : PreservesLimit F (Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.toPresheaf Y) := by
    apply preservesLimit_of_evaluation
    intro V
    change PreservesLimit F (Scheme.Modules.toPresheaf X ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat).obj (op (j ''ᵁ V.unop)))
    haveI : PreservesLimit F (Scheme.Modules.toPresheaf X) := inferInstance
    haveI : PreservesLimit (F ⋙ Scheme.Modules.toPresheaf X)
        ((CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat).obj (op (j ''ᵁ V.unop))) := by
      haveI : HasLimitsOfShape J AddCommGrpCat.{u} := inferInstance
      exact evaluation_preservesLimit (F ⋙ Scheme.Modules.toPresheaf X) _
    exact comp_preservesLimit _ _
  haveI : ReflectsLimit (F ⋙ Scheme.Modules.restrictFunctor j) (Scheme.Modules.toPresheaf Y) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact preservesLimit_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Y)
/-- Restricting the original object retains the exact limiting cone. -/
@[expose] def restrictedIsLimit {Y:Scheme.{u}} (j:Y⟶X) [IsOpenImmersion j] :
    IsLimit ((Scheme.Modules.restrictFunctor j).mapCone (cone U c)) :=
  isLimitOfPreserves (Scheme.Modules.restrictFunctor j) (isLimit U c)
end CocycleModuleCone318
