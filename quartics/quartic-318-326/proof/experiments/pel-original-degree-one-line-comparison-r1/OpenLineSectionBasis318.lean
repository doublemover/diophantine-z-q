module
public import ModuleFreeOpenFrames318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace OpenLineSectionBasis318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit (U:Scheme).ringCatSheaf≅M.restrict U.ι)
/-- The original unit frame transported to the actual site over the open. -/
@[expose] def overFrame:SheafOfModules.unit (X.ringCatSheaf.over U)≅M.over U:=by
  let E:=Scheme.Modules.overEquiv U
  exact E.functor.preimageIso <|
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app M).symm
/-- A line frame gives an actual linear equivalence on the original open's
sections, over the original section ring, not merely at its generic point. -/
@[expose] def sections:Γ(X,U)≃ₗ[Γ(X,U)]Γ(M,U):=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (𝟙 U)))).mapIso (overFrame M U e)).toLinearEquiv
@[expose] def basis:Module.Basis (Fin 1) Γ(X,U) Γ(M,U):=
  (Module.Basis.singleton (Fin 1) Γ(X,U)).map (sections M U e)
variable (V:X.Opens) (h:V≤U)
/-- Restrict the same actual unit frame to a smaller original open. -/
@[expose] def restrictFrame:SheafOfModules.unit (V:Scheme).ringCatSheaf≅M.restrict V.ι:=
  (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).symm.app M) ≪≫
        ((Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X h)).app M)
lemma sections_hom_inv:(sections M U e).toLinearMap.comp (sections M U e).symm.toLinearMap=
    LinearMap.id:=LinearMap.ext (fun s=>(sections M U e).apply_symm_apply s)
lemma sections_inv_hom:(sections M U e).symm.toLinearMap.comp (sections M U e).toLinearMap=
    LinearMap.id:=LinearMap.ext (fun s=>(sections M U e).symm_apply_apply s)
end OpenLineSectionBasis318
