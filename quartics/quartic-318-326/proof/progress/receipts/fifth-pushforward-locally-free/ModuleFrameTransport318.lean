module
public import PushforwardStructureSheaf318
public section
noncomputable section
namespace ModuleFrameTransport318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (e:X≅Y) (M:Y.Modules) (ι:Type u)
/-- Transport an actual frame through an actual Scheme isomorphism, using
restriction functors and their exact composition inverses. -/
@[expose] def alongIso
    (frame:SheafOfModules.free (R:=X.ringCatSheaf) ι≅M.restrict e.hom):
    SheafOfModules.free (R:=Y.ringCatSheaf) ι≅M:=by
  letI : (Scheme.Modules.restrictFunctor e.inv).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction e.inv).isLeftAdjoint
  exact SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor e.inv) ι
      (Scheme.Modules.restrictUnitIso e.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso frame ≪≫
      ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm.app M) ≪≫
      ((Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M) ≪≫
      ((Scheme.Modules.restrictFunctorId (X:=Y)).app M)
/-- An actual affine-Spec frame gives a frame on the original affine open,
retaining its actual inclusion into the ambient Scheme. -/
@[expose] def fromSpec {Z:Scheme.{u}} (N:Z.Modules) (U:Z.Opens)
    (hU:IsAffineOpen U) (I:Type u)
    (frame:SheafOfModules.free (R:=(Spec Γ(Z,U)).ringCatSheaf) I≅N.restrict hU.fromSpec):
    SheafOfModules.free (R:=(U:Scheme).ringCatSheaf) I≅N.restrict U.ι:=
  alongIso hU.isoSpec.symm (N.restrict U.ι) I
    (frame ≪≫ (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app N)
end ModuleFrameTransport318
