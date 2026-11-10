module
public import ContactRelativeTwistedBoundary318
public import ContactCanonicalHOneBaseChange318
public section
noncomputable section
namespace ContactRelativeGeometricVanishing318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeWholeOpenSections318 ContactRelativeGeometricTwist318
open ContactRelativeTwistedCoordinates318 ContactRelativeTwistedBoundary318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)

/-- Genuine relative geometric H1 vanishing for every original line on
every arbitrary coefficient test. All full-chart and twist compatibilities
are constructed; no free basis or reduced/Noetherian hypothesis is added. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ)), x = 0 := by
  obtain ⟨N,hN⟩ := ContactOriginalRelativeOverlapSpan318.exists_bound R c L
  refine ⟨N,fun n hn x => ?_⟩
  obtain ⟨s,rfl⟩ := NonreducedLineMayerVietoris318.boundary_surjective (twist R c L (n : ℤ))
    (finiteOpen R c) (infinityOpen R c) (finite_affine R c) (infinity_affine R c) (cover R c) x
  have hz := hN n hn ((shiftedBoundary R c L (n : ℤ)).mkQ (coordinates R c L (n : ℤ) s))
  have hs : coordinates R c L (n : ℤ) s ∈ shiftedBoundary R c L (n : ℤ) := by
    change Submodule.Quotient.mk (coordinates R c L (n : ℤ) s) = 0 at hz
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  have hd := (difference_iff R c L (n : ℤ) s).mpr hs
  rw [← NonreducedLineMayerVietoris318.kernel_eq_range (twist R c L (n : ℤ))
    (finiteOpen R c) (infinityOpen R c) (cover R c)] at hd
  exact hd

/-- The SAME bound survives EVERY further affine coefficient extension.
The target is the actual geometric pullback of the original twist; no
separate identification with a freshly clutched target twist is assumed. -/
theorem exists_universal_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S),
    ∀ x : NonreducedLineMayerVietoris318.H1
      (ContactOriginalDerivedCoefficientMap318.pulled R S f c (twist R c L (n : ℤ))), x = 0 := by
  obtain ⟨N,hN⟩ := exists_bound R c L
  refine ⟨N,fun n hn S _ f x => ?_⟩
  letI : Algebra R S := f.toAlgebra
  letI : Module R (NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ))) :=
    OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) _ 1
  letI : Module S (NonreducedLineMayerVietoris318.H1
      (ContactOriginalDerivedCoefficientMap318.pulled R S f c (twist R c L (n : ℤ)))) :=
    OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c) _ 1
  let e := ContactOriginalHOneBaseChange318.equivalence R S f c (twist R c L (n : ℤ))
  obtain ⟨z,rfl⟩ := e.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul s y => rw [hN n hn y,tmul_zero,map_zero]
  | add z w hz hw => rw [map_add,hz,hw,add_zero]
end ContactRelativeGeometricVanishing318
