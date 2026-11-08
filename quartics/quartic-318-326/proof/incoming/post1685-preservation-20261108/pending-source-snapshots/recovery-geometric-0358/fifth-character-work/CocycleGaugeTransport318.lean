module
public import CocycleGaugeIso318
public section
noncomputable section
namespace CocycleGaugeTransport318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c c' d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (hc:c=c') (a:∀i,Γ(X,U i)ˣ)
    (h:∀i j,d.transition i j=UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.units X).obj U a i j*c'.transition i j)
lemma eqIso_coefficient (i:ι):
    (eqToIso (congrArg (CocycleModule318.object U) hc)).hom≫CocycleModule318.coefficient U c' i=
      CocycleModule318.coefficient U c i:=by
  cases hc
  simp only [eqToIso_refl,Iso.refl_hom,Category.id_comp]
@[expose] def iso:CocycleModule318.object U c≅CocycleModule318.object U d:=
  eqToIso (congrArg (CocycleModule318.object U) hc)≪≫CocycleGaugeIso318.iso U c' d a h
lemma coefficient (i:ι):
    (iso U c c' d hc a h).hom≫
      CocycleModule318.coefficient U d i=
        CocycleModule318.coefficient U c i≫CocycleGaugeMaps318.scale U a i:=by
  change ((eqToIso (congrArg (CocycleModule318.object U) hc)).hom≫
    (CocycleGaugeIso318.iso U c' d a h).hom)≫_=_
  rw [Category.assoc,CocycleGaugeIso318.hom_coefficient,←Category.assoc,
    eqIso_coefficient U c c' hc i]
end CocycleGaugeTransport318
