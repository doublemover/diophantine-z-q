module
public import FiniteAffineAlgebra318
public import FiniteProjectiveDualFrame318
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public section
noncomputable section
namespace FiniteFlatAffineProjective318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (p : Z ⟶ Spec R)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
/-- Finite as an algebra plus finite algebra presentation gives finite
MODULE presentation; this missing hypothesis is not inferred from finite
flatness alone over a non-Noetherian base. -/
instance finitePresentation : Module.FinitePresentation R (FiniteAffineAlgebra318.ring R p) :=
  Module.FinitePresentation.of_finite_of_finitePresentation R _
instance projective : Module.Projective R (FiniteAffineAlgebra318.ring R p) :=
  FiniteProjectiveDualFrame318.projective_of_finitePresentation_flat R _
/-- Actual global finite free retract of the entire family's function
module, without asserting a global free basis or constant rank. -/
lemma finite_retract : ∃ (n : ℕ)
    (f : (Fin n → R) →ₗ[R] FiniteAffineAlgebra318.ring R p)
    (g : FiniteAffineAlgebra318.ring R p →ₗ[R] (Fin n → R)),
    Function.Surjective f ∧ Function.Injective g ∧ f.comp g=LinearMap.id :=
  Module.Finite.exists_comp_eq_id_of_projective R _
end FiniteFlatAffineProjective318
