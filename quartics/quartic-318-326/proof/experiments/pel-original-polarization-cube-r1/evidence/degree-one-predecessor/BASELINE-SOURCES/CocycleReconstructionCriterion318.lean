module
public import CocycleModule318
public import ModuleOpenIsoCriterion318
public section
noncomputable section
namespace CocycleReconstructionCriterion318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
/-- The original coefficient projection, transposed under the actual open
restriction/pushforward adjunction. -/
@[expose] def projection (i:ι):
    (CocycleModule318.object U c).restrict (U i).ι⟶
      SheafOfModules.unit (U i).toScheme.ringCatSheaf:=
  ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv
    (CocycleModule318.object U c) (SheafOfModules.unit (U i).toScheme.ringCatSheaf)).symm
      (CocycleModule318.coefficient U c i)
variable {M:X.Modules} (s:∀i,M⟶CocycleModule318.chart U i)
    (h:∀i j,s i≫CocycleModule318.left U i j=s j≫CocycleModule318.right U c i j)
lemma lift_projection (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map (CocycleModule318.lift U c s h)≫projection U c i=
      ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv M
        (SheafOfModules.unit (U i).toScheme.ringCatSheaf)).symm (s i):=by
  rw [projection,←Adjunction.homEquiv_naturality_left_symm]
  rw [CocycleModule318.lift_coefficient]
include h in
/-- An exact compatible original coefficient family reconstructs the original
module once its own local coordinate maps and the actual cocycle coefficient
projections are proved isomorphisms. These local premises are explicit. -/
lemma lift_isIso (hc:(⊤:X.Opens)≤⨆i,U i)
    (hp:∀i,IsIso (projection U c i))
    (hs:∀i,IsIso (((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv M
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf)).symm (s i))):
    IsIso (CocycleModule318.lift U c s h):=by
  apply ModuleOpenIsoCriterion318.of_restrictions _ U hc
  intro i
  letI:=hp i
  haveI:IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map
      (CocycleModule318.lift U c s h)≫projection U c i):=by
    rw [lift_projection]
    exact hs i
  exact IsIso.of_isIso_comp_right _ (projection U c i)
end CocycleReconstructionCriterion318
