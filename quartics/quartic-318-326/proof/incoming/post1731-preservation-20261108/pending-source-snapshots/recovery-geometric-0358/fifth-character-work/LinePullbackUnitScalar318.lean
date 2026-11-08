module
public import LinePullbackFrameScalar318
public import UnitSheafScalar318
public section
noncomputable section
namespace LinePullbackUnitScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U:Y.Opens)
    (e0 e1:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
lemma original_relation:
    ClutchedModule318.multiply (UnitSheafScalar318.unit (e1≪≫e0.symm)).val≫e0.hom=e1.hom:=by
  rw [←UnitSheafScalar318.hom_multiply]
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
/-- Exact unit of the actual two pulled frame maps, not merely a value
on field points or a comparison up to an unspecified unit. -/
lemma unit:
    UnitSheafScalar318.unit
      (LinePullbackFrames318.frame f M U e1≪≫(LinePullbackFrames318.frame f M U e0).symm)=
    Units.map (LinePullbackFrames318.chartMap f U).appTop.hom.toMonoidHom
      (UnitSheafScalar318.unit (e1≪≫e0.symm)):=by
  apply UnitSheafScalar318.unique
  have h:=LinePullbackFrameScalar318.relation f M U e0 e1
    (UnitSheafScalar318.unit (e1≪≫e0.symm)).val (original_relation M U e0 e1)
  have h':=congrArg (fun q=>q≫(LinePullbackFrames318.frame f M U e0).inv) h
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Iso.trans_hom,Iso.symm_hom]
    using h'.symm
end LinePullbackUnitScalar318
