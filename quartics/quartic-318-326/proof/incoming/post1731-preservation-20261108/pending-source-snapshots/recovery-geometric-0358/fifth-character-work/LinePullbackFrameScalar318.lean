module
public import LinePullbackFrames318
public import PullbackScalar318
public section
noncomputable section
namespace LinePullbackFrameScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}}
lemma inverse_unit_scalar (f:X⟶Y) (a:Γ(Y,⊤)):
    ClutchedModule318.multiply (f.appTop a)≫(IdentityCotangent318.pullbackUnitIso f).inv=
    (IdentityCotangent318.pullbackUnitIso f).inv≫
      (Scheme.Modules.pullback f).map (ClutchedModule318.multiply a):=by
  have h:=congrArg (fun q=>(IdentityCotangent318.pullbackUnitIso f).inv≫q≫
    (IdentityCotangent318.pullbackUnitIso f).inv)
    (PullbackScalar318.pullback_multiply f a).symm
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.hom_inv_id,Category.comp_id] using h
/-- Exact same-open scalar compatibility of the genuine pulled frames.
The source and target scalars are related by the original restricted
Scheme map, including its complete section-ring map. -/
lemma relation (f:X⟶Y) (M:Y.Modules) (U:Y.Opens)
    (e0 e1:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (a:Γ(U.toScheme,⊤))
    (h:ClutchedModule318.multiply a≫e0.hom=e1.hom):
    ClutchedModule318.multiply ((LinePullbackFrames318.chartMap f U).appTop a)≫
      (LinePullbackFrames318.frame f M U e0).hom=
      (LinePullbackFrames318.frame f M U e1).hom:=by
  change ClutchedModule318.multiply _≫
    ((IdentityCotangent318.pullbackUnitIso (LinePullbackFrames318.chartMap f U)).inv≫
      (Scheme.Modules.pullback (LinePullbackFrames318.chartMap f U)).map e0.hom≫
      (PullbackLineFrames318.chartIso f U.ι (f⁻¹ᵁU).ι
        (LinePullbackFrames318.chartMap f U) (LinePullbackFrames318.square f U) M).inv)=_
  rw [←Category.assoc,inverse_unit_scalar]
  simp only [Category.assoc]
  rw [←Functor.map_comp_assoc,h]
  rfl
end LinePullbackFrameScalar318
