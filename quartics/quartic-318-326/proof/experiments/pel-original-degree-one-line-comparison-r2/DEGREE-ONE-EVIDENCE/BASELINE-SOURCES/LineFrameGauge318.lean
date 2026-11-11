module
public import LineFrameCocycle318
public section
noncomputable section
namespace LineFrameGauge318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type v} (V:ι→X.Opens)
  (e d:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
/-- Old coordinate mapped into the new coordinate, on the entire original
chart. This orientation gives d_ij = a_i*a_j⁻¹*e_ij. -/
@[expose] def unit (i:ι):Γ(X,V i)ˣ:=
  FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame M (V i) (d i) (V i) le_rfl)
    (OpenLineFrameCoordinates318.frame M (V i) (e i) (V i) le_rfl)
lemma restrict (i:ι) (W:X.Opens) (h:W≤V i):
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (unit M V e d i)=
      FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame M (V i) (d i) W h)
        (OpenLineFrameCoordinates318.frame M (V i) (e i) W h):=by
  apply Units.ext
  change X.presheaf.map (homOfLE h).op
    ((OpenLineFrameCoordinates318.frame M (V i) (d i) (V i) le_rfl).symm
      (OpenLineFrameCoordinates318.frame M (V i) (e i) (V i) le_rfl 1))=_
  rw [OpenLineFrameCoordinates318.inverse_natural,OpenLineFrameCoordinates318.natural,map_one]
  rfl
/-- Frame-change identity on any common original subopen. -/
lemma subopen_equation (i j:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j):
    FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame M (V i) (d i) W hi)
      (OpenLineFrameCoordinates318.frame M (V j) (d j) W hj)=
    (Units.map (X.presheaf.map (homOfLE hi).op).hom.toMonoidHom (unit M V e d i)*
      (Units.map (X.presheaf.map (homOfLE hj).op).hom.toMonoidHom (unit M V e d j))⁻¹)*
    FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame M (V i) (e i) W hi)
      (OpenLineFrameCoordinates318.frame M (V j) (e j) W hj):=by
  rw [restrict,restrict]
  exact FrameScalarAlgebra318.gauge _ _ _ _
/-- Genuine frame changes induce precisely the original unit-coboundary
relation, rather than a newly postulated equivalence of cocycle labels. -/
lemma equation (i j:ι):
    (LineFrameCocycle318.cocycle M V d).transition i j=
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units X).obj V
        (unit M V e d) i j * (LineFrameCocycle318.cocycle M V e).transition i j:=by
  change FrameScalarAlgebra318.scalar _ _ =
    (Units.map (X.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom (unit M V e d i)*
      (Units.map (X.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom (unit M V e d j))⁻¹)*_
  rw [restrict,restrict]
  exact FrameScalarAlgebra318.gauge _ _ _ _
lemma equivalent:UnitTransitionCocycle318.GaugeEquivalent
    (LineFrameCocycle318.cocycle M V e) (LineFrameCocycle318.cocycle M V d):=
  ⟨unit M V e d,equation M V e d⟩
end LineFrameGauge318
