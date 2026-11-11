module
public import FramedTensorAssociator318
public import FramedTensorUnit318
public import LineSheafTensor318
public import LineSheafUnit318
public section
noncomputable section
namespace LineSheafTensorIsos318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}}
@[expose] def tripleCover (L N P:Line X):((L.Index×N.Index)×P.Index)→X.Opens:=
  fun i=>(L.opens i.1.1⊓N.opens i.1.2)⊓P.opens i.2
lemma triple_cover (L N P:Line X):(⊤:X.Opens)≤⨆i,tripleCover L N P i:=
  UnitCocycleRefinement318.common_cover (fun i:L.Index×N.Index=>L.opens i.1⊓N.opens i.2)
    P.opens (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover) P.cover
/-- Actual parenthesized tensor sheaves of the original line objects. The
common refinement supplies genuine original frames; its presentation is not
identified with either pre-existing tensor-line cover record. -/
@[expose] def assoc (L N P:Line X):
    (LineSheafTensor318.line (LineSheafTensor318.line L N) P).object≅
      (LineSheafTensor318.line L (LineSheafTensor318.line N P)).object:=
  FramedTensorAssociator318.iso L.object N.object P.object (tripleCover L N P)
    (fun i=>OpenLineFrameRefinement318.frame L.object (L.opens i.1.1) (L.frame i.1.1)
      _ (inf_le_left.trans inf_le_left))
    (fun i=>OpenLineFrameRefinement318.frame N.object (N.opens i.1.2) (N.frame i.1.2)
      _ (inf_le_left.trans inf_le_right))
    (fun i=>OpenLineFrameRefinement318.frame P.object (P.opens i.2) (P.frame i.2) _ inf_le_right)
    (triple_cover L N P)
@[expose] def comm (L N:Line X):
    (LineSheafTensor318.line L N).object≅(LineSheafTensor318.line N L).object:=
  FramedTensorCommutor318.iso L.object N.object (fun i:L.Index×N.Index=>L.opens i.1⊓N.opens i.2)
    (fun i=>OpenLineFrameRefinement318.frame L.object (L.opens i.1) (L.frame i.1) _ inf_le_left)
    (fun i=>OpenLineFrameRefinement318.frame N.object (N.opens i.2) (N.frame i.2) _ inf_le_right)
    (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover)
@[expose] def leftUnit (L:Line X):
    (LineSheafTensor318.line (LineSheafUnit318.line X) L).object≅L.object:=
  FramedTensorUnit318.leftIso L.object L.opens L.frame L.cover
@[expose] def rightUnit (L:Line X):
    (LineSheafTensor318.line L (LineSheafUnit318.line X)).object≅L.object:=
  FramedTensorUnit318.rightIso L.object L.opens L.frame L.cover
lemma assoc_hom_inv (L N P:Line X):(assoc L N P).hom≫(assoc L N P).inv=𝟙 _:=
  (assoc L N P).hom_inv_id
lemma assoc_inv_hom (L N P:Line X):(assoc L N P).inv≫(assoc L N P).hom=𝟙 _:=
  (assoc L N P).inv_hom_id
lemma comm_hom_inv (L N:Line X):(comm L N).hom≫(comm L N).inv=𝟙 _:=
  (comm L N).hom_inv_id
lemma comm_inv_hom (L N:Line X):(comm L N).inv≫(comm L N).hom=𝟙 _:=
  (comm L N).inv_hom_id
lemma left_hom_inv (L:Line X):(leftUnit L).hom≫(leftUnit L).inv=𝟙 _:=
  (leftUnit L).hom_inv_id
lemma left_inv_hom (L:Line X):(leftUnit L).inv≫(leftUnit L).hom=𝟙 _:=
  (leftUnit L).inv_hom_id
lemma right_hom_inv (L:Line X):(rightUnit L).hom≫(rightUnit L).inv=𝟙 _:=
  (rightUnit L).hom_inv_id
lemma right_inv_hom (L:Line X):(rightUnit L).inv≫(rightUnit L).hom=𝟙 _:=
  (rightUnit L).inv_hom_id
end LineSheafTensorIsos318
