module
public import PushforwardGlobalSections318
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique
public section
noncomputable section
namespace TildePullback318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S T : CommRingCat.{u}} (f : S ⟶ T)

/-- Genuine natural identification of affine pushforward global sections with scalar restriction. -/
@[expose] def globalNatIso :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom := by
  exact Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f)
    (TopCat.Sheaf.forget (ModuleCat S) (Spec S) ⋙ (evaluation _ _).obj (Opposite.op ⊤))

/-- Pulling back a genuine affine tilde sheaf is canonically tilde of scalar extension.
    This is obtained from the actual sheaf and module adjunctions, not an assumed tensor comparison. -/
@[expose] def pullbackIso :
    tilde.functor S ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor T :=
  (((tilde.adjunction (R:=S)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
    (globalNatIso f)).leftAdjointUniq
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=T)))

/-- The constructed tilde pullback comparison has the exact adjunction-unit normalization. -/
theorem pullbackIso_adjoint (M : ModuleCat S) :
    let adj1 := ((tilde.adjunction (R:=S)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight (globalNatIso f)
    let adj2 := (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R:=T))
    adj1.homEquiv _ _ ((pullbackIso f).hom.app M) = adj2.unit.app M := by
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ M

/-- Actual restriction on an open immersion is the same canonical scalar-extension tilde object. -/
@[expose] def restrictionIso [IsOpenImmersion (Spec.map f)] :
    tilde.functor S ⋙ Scheme.Modules.restrictFunctor (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor T :=
  Functor.isoWhiskerLeft (tilde.functor S) (Scheme.Modules.restrictFunctorIsoPullback (Spec.map f)) ≪≫
    pullbackIso f
end TildePullback318
