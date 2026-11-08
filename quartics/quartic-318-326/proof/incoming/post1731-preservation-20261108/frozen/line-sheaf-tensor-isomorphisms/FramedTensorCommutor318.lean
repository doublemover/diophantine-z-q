module
public import FramedLineCocycleIso318
public import TensorLineCocycle318
public import UnitCocycleProductLaws318
public section
noncomputable section
namespace FramedTensorCommutor318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (en:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅N.restrict (U i).ι)
lemma cocycle_eq:
    LineFrameCocycle318.cocycle (tensor M N) U (TensorLineCocycle318.frames M N U em en)=
      LineFrameCocycle318.cocycle (tensor N M) U (TensorLineCocycle318.frames N M U en em):=
  (TensorLineCocycle318.cocycle_eq M N U em en).trans
    ((UnitCocycleProductLaws318.comm _ _).trans (TensorLineCocycle318.cocycle_eq N M U en em).symm)
variable (hc:(⊤:X.Opens)≤⨆i,U i)
@[expose] def iso:tensor M N≅tensor N M:=
  FramedLineCocycleIso318.iso _ _ U (TensorLineCocycle318.frames M N U em en)
    (TensorLineCocycle318.frames N M U en em) hc (cocycle_eq M N U em en)
lemma hom_inv:(iso M N U em en hc).hom≫(iso M N U em en hc).inv=𝟙 _:=
  (iso M N U em en hc).hom_inv_id
lemma inv_hom:(iso M N U em en hc).inv≫(iso M N U em en hc).hom=𝟙 _:=
  (iso M N U em en hc).inv_hom_id
end FramedTensorCommutor318
