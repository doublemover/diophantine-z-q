module
public import FiniteUnitTransferSourceIso318
public import StructureLineCocycleIso318
public section
noncomputable section
namespace FiniteUnitTransferUnit318
open AlgebraicGeometry CategoryTheory UnitTransferGaugeIso318 FiniteUnitTransferPresentation318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    {ι:Type u} (U:ι→Y.Opens)
@[expose] def sourceFrames (i:ι):
    SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅
      Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) (f⁻¹ᵁU i).ι:=
  StructureLineFrames318.frame X (f⁻¹ᵁU i)
lemma source_cocycle_eq:
    InverseImageLineCocycle318.cocycle f (SheafOfModules.unit X.ringCatSheaf) U (sourceFrames f U)=
      UnitCocycleOne318.one (StructureUnitsSheaf318.pushedUnits f).obj U:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact StructureLineFrames318.inverseImage_transition_one X f U i j
lemma target_cocycle_eq:
    transfer f unitMap U (InverseImageLineCocycle318.cocycle f
      (SheafOfModules.unit X.ringCatSheaf) U (sourceFrames f U))=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units Y).obj U:=by
  rw [source_cocycle_eq]
  exact UnitCocycleOne318.map_one unitMap.hom U
/-- The original structure line, with identity coordinate frames, transfers
to the original target structure module through the actual constant-one iso. -/
@[expose] def fixedIso (hc:(⊤:Y.Opens)≤⨆i,U i):
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f
      (SheafOfModules.unit X.ringCatSheaf) U (sourceFrames f U)))≅SheafOfModules.unit Y.ringCatSheaf:=
  CocycleEqualityTransport318.iso U (target_cocycle_eq f unitMap U)≪≫
    (StructureLineCocycleIso318.iso Y U hc).symm
variable [IsFinite f] (M:X.Modules) (e:M≅SheafOfModules.unit X.ringCatSheaf)
    {α:Type u} (A:α→X.Opens) (hA:(⊤:X.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
/-- Any actual trivialization of the original source line produces an actual
target trivialization for its independently supplied covering presentation. -/
@[expose] def iso:FiniteUnitTransferLine318.object f M A hA eA unitMap≅
    SheafOfModules.unit Y.ringCatSheaf:=
  FiniteUnitTransferSourceIso318.fixedIso f unitMap e (targetOpen f M A hA eA)
    (sourceFrame f M A hA eA) (sourceFrames f (targetOpen f M A hA eA))≪≫
  fixedIso f unitMap (targetOpen f M A hA eA) (target_cover f M A hA eA)
lemma hom_inv:(iso f unitMap M e A hA eA).hom≫(iso f unitMap M e A hA eA).inv=𝟙 _ :=
  (iso f unitMap M e A hA eA).hom_inv_id
lemma inv_hom:(iso f unitMap M e A hA eA).inv≫(iso f unitMap M e A hA eA).hom=𝟙 _ :=
  (iso f unitMap M e A hA eA).inv_hom_id
end FiniteUnitTransferUnit318
