module
public import OriginalOpenPullbackSections318
public section
noncomputable section
namespace OriginalOpenPullbackSectionScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)

/-- The original full-image section comparison preserves the ACTUAL
coefficient change, through the original open-immersion ring isomorphism. -/
lemma scalar (a : Γ(X,⊤)) (s : Γ((Scheme.Modules.pullback f).obj M,⊤)) :
    OriginalOpenPullbackSections318.sectionsEquiv f M (a • s) =
      ((f.appIso ⊤).inv a) • OriginalOpenPullbackSections318.sectionsEquiv f M s :=
  ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).app_smul a s
end OriginalOpenPullbackSectionScalar318
