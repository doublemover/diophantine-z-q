module
public import FramedLineCocycleIso318
public import TensorLineCocycle318
public import UnitCocycleProductLaws318
public section
noncomputable section
namespace FramedTensorAssociator318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N P:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (en:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅N.restrict (U i).ι)
    (ep:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅P.restrict (U i).ι)
@[expose] def leftFrames:=TensorLineCocycle318.frames (tensor M N) P U
  (TensorLineCocycle318.frames M N U em en) ep
@[expose] def rightFrames:=TensorLineCocycle318.frames M (tensor N P) U
  em (TensorLineCocycle318.frames N P U en ep)
lemma cocycle_eq:
    LineFrameCocycle318.cocycle (tensor (tensor M N) P) U (leftFrames M N P U em en ep)=
      LineFrameCocycle318.cocycle (tensor M (tensor N P)) U (rightFrames M N P U em en ep):=by
  have hl:=(TensorLineCocycle318.cocycle_eq (tensor M N) P U
    (TensorLineCocycle318.frames M N U em en) ep).trans
    (congrArg (fun c=>UnitCocycleProduct318.product c (LineFrameCocycle318.cocycle P U ep))
      (TensorLineCocycle318.cocycle_eq M N U em en))
  have hr:=(TensorLineCocycle318.cocycle_eq M (tensor N P) U
    em (TensorLineCocycle318.frames N P U en ep)).trans
    (congrArg (fun c=>UnitCocycleProduct318.product (LineFrameCocycle318.cocycle M U em) c)
      (TensorLineCocycle318.cocycle_eq N P U en ep))
  exact hl.trans ((UnitCocycleProductLaws318.assoc _ _ _).trans hr.symm)
variable (hc:(⊤:X.Opens)≤⨆i,U i)
/-- An actual isomorphism of the two original parenthesized tensor sheaves,
constructed from the specified genuine common-cover frames. -/
@[expose] def iso:tensor (tensor M N) P≅tensor M (tensor N P):=
  FramedLineCocycleIso318.iso _ _ U (leftFrames M N P U em en ep)
    (rightFrames M N P U em en ep) hc (cocycle_eq M N P U em en ep)
lemma hom_inv:(iso M N P U em en ep hc).hom≫(iso M N P U em en ep hc).inv=𝟙 _:=
  (iso M N P U em en ep hc).hom_inv_id
lemma inv_hom:(iso M N P U em en ep hc).inv≫(iso M N P U em en ep hc).hom=𝟙 _:=
  (iso M N P U em en ep hc).inv_hom_id
end FramedTensorAssociator318
