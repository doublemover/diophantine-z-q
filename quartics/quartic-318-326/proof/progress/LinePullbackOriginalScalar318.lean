module
public import LinePullbackUnitScalar318
public import LineFrameTopScalar318
public section
noncomputable section
namespace LinePullbackOriginalScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U:Y.Opens)
lemma ring_square:
    (LinePullbackFrames318.chartMap f U).appTop≫(LineFrameTopScalar318.ringTop (f⁻¹ᵁU)).hom=
    (LineFrameTopScalar318.ringTop U).hom≫f.app U:=by
  have h:=(arrowResLEAppIso f U (f⁻¹ᵁU) le_rfl).hom.w
  change U.topIso.hom≫f.appLE U (f⁻¹ᵁU) le_rfl=
    (f.resLE U (f⁻¹ᵁU) le_rfl).appTop≫(f⁻¹ᵁU).topIso.hom at h
  have ht (Z:Scheme.{u}) (V:Z.Opens):(LineFrameTopScalar318.ringTop V).hom=V.topIso.hom:=by
    rw [LineFrameTopScalar318.ringTop_hom,Scheme.Opens.topIso_hom]
    congr 1
  rw [ht X (f⁻¹ᵁU),ht Y U]
  simpa only [LinePullbackFrames318.chartMap,Scheme.Hom.appLE_eq_app] using h.symm
/-- Same-open comparison in the original ambient section rings, including
the actual f.app U map and not only an isomorphic subscheme ring. -/
lemma scalar (e0 e1:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU)
        (LinePullbackFrames318.frame f M U e0) (f⁻¹ᵁU) le_rfl)
      (OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU)
        (LinePullbackFrames318.frame f M U e1) (f⁻¹ᵁU) le_rfl)=
    Units.map (f.app U).hom.toMonoidHom (FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame M U e0 U le_rfl)
      (OpenLineFrameCoordinates318.frame M U e1 U le_rfl)):=by
  rw [←LineFrameTopScalar318.scalar,←LineFrameTopScalar318.scalar,LinePullbackUnitScalar318.unit]
  apply Units.ext
  change (LineFrameTopScalar318.ringTop (f⁻¹ᵁU)).hom
    ((LinePullbackFrames318.chartMap f U).appTop (UnitSheafScalar318.unit (e1≪≫e0.symm)).val)=
    f.app U ((LineFrameTopScalar318.ringTop U).hom (UnitSheafScalar318.unit (e1≪≫e0.symm)).val)
  exact congrArg (fun q=>q (UnitSheafScalar318.unit (e1≪≫e0.symm)).val) (ring_square f U)
end LinePullbackOriginalScalar318
