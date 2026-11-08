module
public import LineFrameReconstructionIso318
public import FifthLineExtractedCocycle318
public section
noncomputable section
namespace FifthLineReconstruction318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Model.Modules) {κ:Type} (V:κ→Model.Opens)
    (hc:(⊤:Model.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
abbrev targetOpen:=FifthLineTargetCover318.neighborhood M V hc frames
abbrev sourceOpen (y:Target):Model.Opens:=map⁻¹ᵁtargetOpen M V hc frames y
abbrev sourceFrame:=FifthLineTargetCover318.frame M V hc frames
abbrev sourceCocycle:=LineFrameCocycle318.cocycle M (sourceOpen M V hc frames)
  (sourceFrame M V hc frames)
/-- Exact reconstruction on the genuine complete inverse-image cover,
with the unchanged original source line as domain. -/
@[expose] def sourceIso:M≅CocycleModule318.object (sourceOpen M V hc frames)
    (sourceCocycle M V hc frames):=
  LineFrameReconstructionIso318.iso M (sourceOpen M V hc frames)
    (sourceFrame M V hc frames) (FifthLineTargetCover318.preimage_cover_top M V hc frames)
lemma hom_inv:(sourceIso M V hc frames).hom≫(sourceIso M V hc frames).inv=𝟙 M:=
  (sourceIso M V hc frames).hom_inv_id
lemma inv_hom:(sourceIso M V hc frames).inv≫(sourceIso M V hc frames).hom=𝟙 _:=
  (sourceIso M V hc frames).inv_hom_id
lemma hom_coefficient (i:Target):
    (sourceIso M V hc frames).hom≫CocycleModule318.coefficient
      (sourceOpen M V hc frames) (sourceCocycle M V hc frames) i=
      LineFrameAdjunction318.coordinate M (sourceOpen M V hc frames i)
        (sourceFrame M V hc frames i):=
  LineFrameReconstructionIso318.hom_coefficient _ _ _ _ i
/-- The source cocycle actually used for reconstruction agrees, under the
literal original overlap restriction, with the pushed-unit cocycle to be normed. -/
lemma original_transition (i j:Target):
    Units.map (Model.presheaf.map (homOfLE (show
      map⁻¹ᵁ(targetOpen M V hc frames i⊓targetOpen M V hc frames j)≤
        sourceOpen M V hc frames i⊓sourceOpen M V hc frames j from
          le_inf (map.preimage_mono inf_le_left) (map.preimage_mono inf_le_right))).op).hom.toMonoidHom
      ((sourceCocycle M V hc frames).transition i j)=
      (FifthLineExtractedCocycle318.source M V hc frames).transition i j:=by
  exact LineFrameTransitions318.restrict M (sourceOpen M V hc frames)
    (sourceFrame M V hc frames) i j inf_le_left inf_le_right _
end FifthLineReconstruction318
