module
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace FiniteClosedInOpen318
open AlgebraicGeometry CategoryTheory
universe u
variable {Z U X B : Scheme.{u}} (i : Z ⟶ U) (j : U ⟶ X) (p : X ⟶ B)
  [IsClosedImmersion i] [IsOpenImmersion j] [IsSeparated p] [IsFinite ((i ≫ j) ≫ p)]
/-- A quotient closed in an open chart and finite over the coefficient
base is closed in the ENTIRE separated source, not merely locally closed. -/
lemma closed : IsClosedImmersion (i ≫ j) := by
  letI : UniversallyClosed (i ≫ j) := UniversallyClosed.of_comp_of_isSeparated (i ≫ j) p
  apply IsClosedImmersion.of_isPreimmersion
  simpa only [Set.image_univ] using (i ≫ j).isClosedMap _ isClosed_univ
end FiniteClosedInOpen318
