module
public import FifthLineReconstruction318
public section
noncomputable section
namespace FifthNormLineObject318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318 FifthLineReconstruction318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Model.Modules) {κ:Type} (V:κ→Model.Opens)
    (hc:(⊤:Model.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
/-- The genuine target O-module sheaf clutched by the actual regular-unit
norms of the original source line's constructed transition functions. -/
@[expose] def object:Target.Modules:=CocycleModule318.object
  (targetOpen M V hc frames) (FifthLineExtractedCocycle318.target M V hc frames)
@[expose] def frame (y:Target):
    SheafOfModules.unit (targetOpen M V hc frames y).toScheme.ringCatSheaf≅
      (object M V hc frames).restrict (targetOpen M V hc frames y).ι:=
  (CocycleActualLocalFrame318.frame (targetOpen M V hc frames)
    (FifthLineExtractedCocycle318.target M V hc frames) y).symm
lemma frame_hom_inv (y:Target):(frame M V hc frames y).hom≫(frame M V hc frames y).inv=𝟙 _:=
  (frame M V hc frames y).hom_inv_id
lemma frame_inv_hom (y:Target):(frame M V hc frames y).inv≫(frame M V hc frames y).hom=𝟙 _:=
  (frame M V hc frames y).inv_hom_id
lemma locallyFree:(object M V hc frames).IsLocallyFree:=
  CocycleActualLocalFrame318.locallyFree _ _ (FifthLineTargetCover318.cover_top M V hc frames)
/-- The target transition is the actual norm of the original reconstructed
source transition, transported only across the literal preimage intersection. -/
lemma norm_original_transition (i j:Target):
    (FifthLineExtractedCocycle318.target M V hc frames).transition i j=
      FifthOpenNorm318.unitNorm.app (op (targetOpen M V hc frames i⊓targetOpen M V hc frames j))
        (Units.map (Model.presheaf.map (homOfLE (show
          map⁻¹ᵁ(targetOpen M V hc frames i⊓targetOpen M V hc frames j)≤
            sourceOpen M V hc frames i⊓sourceOpen M V hc frames j from
              le_inf (map.preimage_mono inf_le_left) (map.preimage_mono inf_le_right))).op).hom.toMonoidHom
          ((sourceCocycle M V hc frames).transition i j)):=by
  rw [original_transition]
  rfl
lemma coefficients (i j:Target):
    CocycleModule318.coefficient (targetOpen M V hc frames)
      (FifthLineExtractedCocycle318.target M V hc frames) i≫
      CocycleModule318.left (targetOpen M V hc frames) i j=
    CocycleModule318.coefficient (targetOpen M V hc frames)
      (FifthLineExtractedCocycle318.target M V hc frames) j≫
      CocycleModule318.right (targetOpen M V hc frames)
        (FifthLineExtractedCocycle318.target M V hc frames) i j:=
  CocycleModule318.compatible _ _ i j
end FifthNormLineObject318
