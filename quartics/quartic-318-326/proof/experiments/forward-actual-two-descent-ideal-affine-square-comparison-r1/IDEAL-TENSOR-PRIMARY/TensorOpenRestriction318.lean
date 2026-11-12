module
public import TensorScalarIso318
public import OpenSheafification318
public section
noncomputable section
namespace TensorOpenRestriction318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

@[expose] def coefficientEquiv (U : X.Opens) :
    Γ(X,U) ≃+* Γ(Y,j.opensFunctor.obj U) :=
  (j.appIso U).symm.commRingCatIsoToRingEquiv

/-- New continuation: pointwise tensor compatibility for the actual open coefficient map. -/
@[expose] def presheafIso (M N : Y.Modules) :
    (OpenSheafification318.restriction j).obj (IntrinsicTensorSheaf318.presheaf M N) ≅
      IntrinsicTensorSheaf318.presheaf (M.restrict j) (N.restrict j) :=
  PresheafOfModulesOfCommRing.isoMk
    (fun U => (TensorScalarIso318.tensorEquiv (coefficientEquiv j U.unop)
      (M.val.obj (op (j.opensFunctor.obj U.unop)))
      (N.val.obj (op (j.opensFunctor.obj U.unop)))).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul m n => rfl
      | add a b ha hb => simpa only [map_add,ha,hb])

/-- New continuation: genuine sheaf tensor products commute with actual open restriction. -/
@[expose] def iso (M N : Y.Modules) :
    (IntrinsicTensorSheaf318.tensor M N).restrict j ≅
      IntrinsicTensorSheaf318.tensor (M.restrict j) (N.restrict j) :=
  (OpenSheafification318.iso j (IntrinsicTensorSheaf318.presheaf M N)).symm ≪≫
    (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
      (presheafIso j M N)
end TensorOpenRestriction318
