module
public import LineFrameCocycleReconstruction318
public import CocycleActualLocalFrame318
public section
noncomputable section
namespace LineFrameReconstructionIso318
open AlgebraicGeometry CategoryTheory
open LineFrameCocycleReconstruction318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hc:(⊤:X.Opens)≤⨆i,U i)
include hc in
/-- Reconstruction of the original module from its actual original frames:
the exact original coefficient morphism is an isomorphism. -/
lemma map_isIso:IsIso (map M U frames):=by
  apply isIso_of_projection M U frames hc
  intro i
  change IsIso (CocycleActualLocalFrame318.transpose U (cocycle M U frames) i)
  infer_instance
/-- The original line, not a replacement assumed isomorphic to it, is the
actual coefficient module of its extracted transition functions. -/
@[expose] def iso:M≅CocycleModule318.object U (cocycle M U frames):=by
  letI:=map_isIso M U frames hc
  exact asIso (map M U frames)
lemma hom_eq:(iso M U frames hc).hom=map M U frames:=rfl
lemma hom_inv:(iso M U frames hc).hom≫(iso M U frames hc).inv=𝟙 M:=
  (iso M U frames hc).hom_inv_id
lemma inv_hom:(iso M U frames hc).inv≫(iso M U frames hc).hom=𝟙 _:=
  (iso M U frames hc).inv_hom_id
lemma hom_coefficient (i:ι):
    (iso M U frames hc).hom≫CocycleModule318.coefficient U (cocycle M U frames) i=
      LineFrameAdjunction318.coordinate M (U i) (frames i):=
  map_coefficient M U frames i
lemma inv_coordinate (i:ι):
    (iso M U frames hc).inv≫LineFrameAdjunction318.coordinate M (U i) (frames i)=
      CocycleModule318.coefficient U (cocycle M U frames) i:=by
  rw [←hom_coefficient M U frames hc i,←Category.assoc,inv_hom,Category.id_comp]
lemma original_frame (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map (iso M U frames hc).hom≫
      CocycleActualLocalFrame318.transpose U (cocycle M U frames) i=(frames i).inv:=
  map_projection M U frames i
end LineFrameReconstructionIso318
