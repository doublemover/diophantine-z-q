module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace PushforwardGlobalSections318
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S T : CommRingCat.{u}} (f : S ⟶ T)

/-- Genuine global sections of the actual affine pushforward, with the actual restricted
    scalar action, via Mathlib's pushforward/sheaf compatibility. -/
@[expose] def globalIso (M : (Spec T).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj M) ≅
      (ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj M) := by
  exact (TopCat.Sheaf.forget (ModuleCat S) (Spec S) ⋙
    (evaluation _ _).obj (op ⊤)).mapIso ((pushforwardCompModulesSpecToSheafIso f).app M)
end PushforwardGlobalSections318
