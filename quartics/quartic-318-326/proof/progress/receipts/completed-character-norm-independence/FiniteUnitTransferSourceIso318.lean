module
public import UnitTransferCoverIso318
public import FiniteUnitTransferLine318
public import LineFrameIsoCocycle318
public section
noncomputable section
namespace FiniteUnitTransferSourceIso318
open AlgebraicGeometry CategoryTheory UnitTransferGaugeIso318 FiniteUnitTransferPresentation318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    {M N:X.Modules} (e:M≅N) {ι:Type u} (U:ι→Y.Opens)
    (frames:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
    (newFrames:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (f⁻¹ᵁU i).ι)
abbrev transported:=LineFrameIsoCocycle318.transported e (fun i=>f⁻¹ᵁU i) frames
lemma fixed_cocycle_eq:
    transfer f unitMap U (InverseImageLineCocycle318.cocycle f N U (transported f e U frames))=
      transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U frames):=
  congrArg (transfer f unitMap U) (LineFrameIsoCocycle318.inverseImage_eq e f U frames)
/-- Exact source-isomorphism transport on a specified whole-preimage family. -/
@[expose] def fixedIso:
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U frames))≅
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f N U newFrames)):=
  eqToIso (congrArg (CocycleModule318.object U) (fixed_cocycle_eq f unitMap e U frames).symm)≪≫
    UnitTransferGaugeIso318.ofOriginalFrames f unitMap U N (transported f e U frames) newFrames
variable [IsFinite f] {α β:Type u} (A:α→X.Opens) (B:β→X.Opens)
    (hA:(⊤:X.Opens)≤⨆i,A i) (hB:(⊤:X.Opens)≤⨆j,B j)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
/-- The exact constructed target lines from two independently supplied
original source presentations are genuinely isomorphic when the original
source modules are, via actual source-frame transport and full-cover comparison. -/
@[expose] def iso:
    FiniteUnitTransferLine318.object f M A hA eA unitMap≅
      FiniteUnitTransferLine318.object f N B hB eB unitMap:=
  fixedIso f unitMap e (targetOpen f M A hA eA) (sourceFrame f M A hA eA)
    (LineFrameIsoCocycle318.transported e (sourceOpen f M A hA eA) (sourceFrame f M A hA eA))≪≫
  UnitTransferCoverIso318.iso f unitMap N (targetOpen f M A hA eA) (targetOpen f N B hB eB)
    (LineFrameIsoCocycle318.transported e (sourceOpen f M A hA eA) (sourceFrame f M A hA eA))
    (sourceFrame f N B hB eB) (target_cover f M A hA eA) (target_cover f N B hB eB)
lemma hom_inv:(iso f unitMap e A B hA hB eA eB).hom≫(iso f unitMap e A B hA hB eA eB).inv=𝟙 _ :=
  (iso f unitMap e A B hA hB eA eB).hom_inv_id
lemma inv_hom:(iso f unitMap e A B hA hB eA eB).inv≫(iso f unitMap e A B hA hB eA eB).hom=𝟙 _ :=
  (iso f unitMap e A B hA hB eA eB).inv_hom_id
end FiniteUnitTransferSourceIso318
