module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace ClosedImmersionOpenLift318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion i] [IsOpenImmersion j] (h : Set.range i ⊆ Set.range j)
/-- Factoring an entire closed family through an open source chart retains
its actual closed immersion, including all nilpotent ideal data. -/
instance closed : IsClosedImmersion (IsOpenImmersion.lift j i h) :=
  MorphismProperty.of_isPullback (IsOpenImmersion.isPullback_lift_id i j h).flip inferInstance
end ClosedImmersionOpenLift318
