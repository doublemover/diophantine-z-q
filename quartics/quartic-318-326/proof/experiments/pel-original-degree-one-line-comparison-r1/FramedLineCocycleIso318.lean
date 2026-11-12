module
public import LineFrameReconstructionIso318
public import CocycleEqualityTransport318
public section
noncomputable section
namespace FramedLineCocycleIso318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 250000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (en:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅N.restrict (U i).ι)
    (hc:(⊤:X.Opens)≤⨆i,U i)
    (h:LineFrameCocycle318.cocycle M U em=LineFrameCocycle318.cocycle N U en)
/-- Comparison of unchanged original module sheaves through their genuine
frames and exact extracted cocycle equality. -/
@[expose] def iso:M≅N:=
  CocycleEqualityTransport318.changeTarget U (LineFrameReconstructionIso318.iso M U em hc) h ≪≫
    (LineFrameReconstructionIso318.iso N U en hc).symm
lemma hom_inv:(iso M N U em en hc h).hom≫(iso M N U em en hc h).inv=𝟙 M:=
  (iso M N U em en hc h).hom_inv_id
lemma inv_hom:(iso M N U em en hc h).inv≫(iso M N U em en hc h).hom=𝟙 N:=
  (iso M N U em en hc h).inv_hom_id
/-- The comparison preserves the two supplied original coordinate maps. -/
lemma coordinate (i:ι):
    (iso M N U em en hc h).hom≫LineFrameAdjunction318.coordinate N (U i) (en i)=
      LineFrameAdjunction318.coordinate M (U i) (em i):=by
  rw [iso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    LineFrameReconstructionIso318.inv_coordinate,
    CocycleEqualityTransport318.changeTarget_coefficient,
    LineFrameReconstructionIso318.hom_coefficient]
end FramedLineCocycleIso318
