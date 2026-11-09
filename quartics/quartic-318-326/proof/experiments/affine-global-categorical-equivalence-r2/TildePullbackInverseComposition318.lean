module
public import TildePullbackIdentity318
public section
noncomputable section
namespace TildePullbackInverseComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

/-- Inverse orientation of the actual canonical composition square, ready
for the original affine line-sheaf comparison. -/
lemma composition (M : ModuleCat R) :
    (TildePullback318.pullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
      (Scheme.Modules.pullback (Spec.map g)).map ((TildePullback318.pullbackIso f).inv.app M) ≫
      (AffineComparisonMates318.pullbackComp f g).hom.app ((tilde.functor R).obj M) =
    (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) ≫
      (TildePullback318.pullbackIso (f ≫ g)).inv.app M := by
  let a := (TildePullback318.pullbackIso (f ≫ g)).app M
  let b := (tilde.functor T).mapIso ((ModuleCat.extendScalarsComp f.hom g.hom).app M)
  let c := ((AffineComparisonMates318.pullbackComp f g).app ((tilde.functor R).obj M)).symm
  let d := (Scheme.Modules.pullback (Spec.map g)).mapIso
    ((TildePullback318.pullbackIso f).app M)
  let e := (TildePullback318.pullbackIso g).app ((ModuleCat.extendScalars f.hom).obj M)
  have h : a ≪≫ b = c ≪≫ d ≪≫ e := Iso.ext
    (TildePullbackComposition318.composition_app f g M)
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using
    (congrArg Iso.inv h).symm
end TildePullbackInverseComposition318
