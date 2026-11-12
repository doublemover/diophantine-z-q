module
public import ContactOriginalLaurentBoundary318
public import Mathlib.LinearAlgebra.Isomorphisms
public section
noncomputable section
namespace ContactOriginalLineHOneFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentCoordinates318 ContactOriginalCohomologyCoordinates318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The exact Laurent quotient produced from the SAME original arbitrary
line is rational-linearly isomorphic to its ORIGINAL global derived H1.
The target action comes from actual coefficient endomorphisms. -/
def equivalence : LaurentCechFinite318.H1 (transition c L) ≃ₗ[ℚ] H1 c L :=
  (Submodule.quotEquivOfEq _ _ (ContactOriginalLaurentBoundary318.kernel_eq_boundary c L).symm).trans
    ((boundaryLinear c L).quotKerEquivOfSurjective (boundary_surjective c L))

/-- Every original quotient representative goes to its exact original
derived boundary; the comparison is not chosen by dimension. -/
lemma equivalence_mk (v : LaurentVectorFiltration318.V ℚ (finiteRank c L)) :
    equivalence c L (Submodule.Quotient.mk v) = boundaryLinear c L v := rfl

/-- Genuine finite-dimensionality of global derived H1 for EVERY original
line on the complete Contact model, with the original structural Q action.
No free transition, vanishing assumption, or cohomology comparison is input. -/
instance finite : FiniteDimensional ℚ (H1 c L) := by
  letI := coordinate_h1_finite c L
  exact Module.Finite.of_surjective (equivalence c L).toLinearMap (equivalence c L).surjective

lemma actual_scalar (a : ℚ) (x : H1 c L) :
    a • x = Sheaf.H.map
      (OriginalLineRationalCohomology318.multiply
        (ContactIntrinsicDifferentials318.structureMap c) L a) 1 x := rfl
end ContactOriginalLineHOneFinite318
