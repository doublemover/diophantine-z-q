module
public import CompletedCharacterNormIndependence318
public import FramedLineTensorPower318
public import CocycleEqualityTransport318
public section
noncomputable section
namespace CompletedCharacterPulledCocycle318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 UnitTransferGaugeIso318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (i:Fin 4) {ι:Type} (U:ι→(Target i).Opens)
abbrev TargetCocycle:=UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units (Target i)).obj U
/-- Pullback of the original whole-overlap transition units through the
actual original completed character map. Actual sheaf-frame extraction is
not asserted by this definition. -/
@[expose] def pullback (c:TargetCocycle i U):SourceCocycle (completedMap i) U:=
  UnitTransitionCocycle318.map (CompletedCharacterSheafNorm318.pullback i).hom c
/-- The actual regular norm of the pulled transition cocycle is its literal
eighth power on all original overlaps, including empty overlaps. -/
lemma transfer_eq (c:TargetCocycle i U):
    transfer (completedMap i) (CompletedCharacterSheafNorm318.norm i) U (pullback i U c)=
      UnitCocyclePower318.power c 8:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro j k
  exact CompletedCharacterOpenNorm318.unit_pullback i (U j⊓U k) (c.transition j k)
/-- Actual target eighth tensor compared with the normed pulled coefficient
module. The source module-pullback identification is a separate join. -/
@[expose] def iso (M:(Target i).Modules)
    (em:∀j,SheafOfModules.unit (U j).toScheme.ringCatSheaf≅M.restrict (U j).ι)
    (hc:(⊤:(Target i).Opens)≤⨆j,U j):
    CocycleModule318.object U (transfer (completedMap i) (CompletedCharacterSheafNorm318.norm i) U
      (pullback i U (LineFrameCocycle318.cocycle M U em)))≅
    FramedLineTensorPower318.object M 8:=
  CocycleEqualityTransport318.iso U (transfer_eq i U _)≪≫
    (FramedLineTensorPower318.eighthIso M U em hc).symm
lemma hom_inv (M:(Target i).Modules)
    (em:∀j,SheafOfModules.unit (U j).toScheme.ringCatSheaf≅M.restrict (U j).ι)
    (hc:(⊤:(Target i).Opens)≤⨆j,U j):
    (iso i U M em hc).hom≫(iso i U M em hc).inv=𝟙 _ :=(iso i U M em hc).hom_inv_id
lemma inv_hom (M:(Target i).Modules)
    (em:∀j,SheafOfModules.unit (U j).toScheme.ringCatSheaf≅M.restrict (U j).ι)
    (hc:(⊤:(Target i).Opens)≤⨆j,U j):
    (iso i U M em hc).inv≫(iso i U M em hc).hom=𝟙 _ :=(iso i U M em hc).inv_hom_id
end CompletedCharacterPulledCocycle318
