module
public import OpenLineSectionBasis318
public import UnitModuleScalar318
public section
noncomputable section
namespace OpenLineFrameCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (V:X.Opens)
    (e:SheafOfModules.unit (V:Scheme).ringCatSheaf≅M.restrict V.ι)
/-- Every original subopen's section frame from the same actual sheaf
isomorphism, so its restriction maps are retained rather than re-chosen. -/
@[expose] def frame (W:X.Opens) (h:W≤V):Γ(X,W)≃ₗ[Γ(X,W)]Γ(M,W):=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over V) (op (Over.mk (homOfLE h)))).mapIso
    (OpenLineSectionBasis318.overFrame M V e)).toLinearEquiv
lemma natural {W Z:X.Opens} (hZ:Z≤V) (hWZ:W≤Z) (s:Γ(X,Z)):
    M.presheaf.map (homOfLE hWZ).op (frame M V e Z hZ s)=
      frame M V e W (hWZ.trans hZ) (X.presheaf.map (homOfLE hWZ).op s):=by
  let k:Over.mk (homOfLE (hWZ.trans hZ))⟶Over.mk (homOfLE hZ):=
    Over.homMk (homOfLE hWZ) (Subsingleton.elim _ _)
  exact (congrArg (fun g=>g s)
    ((OpenLineSectionBasis318.overFrame M V e).hom.val.naturality k.op)).symm
lemma inverse_natural {W Z:X.Opens} (hZ:Z≤V) (hWZ:W≤Z) (s:Γ(M,Z)):
    X.presheaf.map (homOfLE hWZ).op ((frame M V e Z hZ).symm s)=
      (frame M V e W (hWZ.trans hZ)).symm (M.presheaf.map (homOfLE hWZ).op s):=by
  let k:Over.mk (homOfLE (hWZ.trans hZ))⟶Over.mk (homOfLE hZ):=
    Over.homMk (homOfLE hWZ) (Subsingleton.elim _ _)
  exact (congrArg (fun g=>g s)
    ((OpenLineSectionBasis318.overFrame M V e).inv.val.naturality k.op)).symm
end OpenLineFrameCoordinates318
