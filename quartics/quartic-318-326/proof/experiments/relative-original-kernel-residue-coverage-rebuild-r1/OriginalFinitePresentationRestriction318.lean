module
public import OriginalLineFiniteFlatPID318
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OriginalFinitePresentationRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (R B : CommRingCat.{u}) [Algebra R B] [Module.FinitePresentation R B]
  (L : Line (Spec B))

/-- The original line module is finitely presented over the original
base chart, by transitivity through its actual finite-presentation algebra.
This does not use a finite-kernel inference over a noncoherent ring. -/
theorem sections : Module.FinitePresentation R (OriginalLineFiniteFlatPID318.pushed R B L) := by
  letI : Module.FinitePresentation B (OriginalLineFiniteFlatPID318.pushed R B L) :=
    (OriginalLineAffineModel318.properties B L).1
  exact Module.FinitePresentation.trans R (OriginalLineFiniteFlatPID318.pushed R B L) B
end OriginalFinitePresentationRestriction318
