module
public import ContactCanonicalHOneBaseChange318
public section
noncomputable section
namespace ContactHOneVanishingBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalDerivedCoefficientMap318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (h : ∀ x : NonreducedLineMayerVietoris318.H1 L, x = 0)
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)

include h in
/-- Actual vanishing propagates through the canonical original H1
isomorphism after ANY further coefficient extension. -/
lemma vanishes (x : NonreducedLineMayerVietoris318.H1 (pulled R S f c L)) : x = 0 := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R (NonreducedLineMayerVietoris318.H1 L) :=
    OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
  letI : Module S (NonreducedLineMayerVietoris318.H1 (pulled R S f c L)) :=
    OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c) _ 1
  let e := ContactOriginalHOneBaseChange318.equivalence R S f c L
  obtain ⟨z,rfl⟩ := e.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul s y => rw [h y,tmul_zero,map_zero]
  | add z w hz hw => rw [map_add,hz,hw,add_zero]
end ContactHOneVanishingBaseChange318
