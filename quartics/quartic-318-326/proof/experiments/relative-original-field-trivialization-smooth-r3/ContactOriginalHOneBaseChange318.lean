module
public import ContactCoefficientCechBaseChange318
public section
noncomputable section
namespace ContactOriginalHOneBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open ContactCoefficientNativeSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
local instance : Module S (NonreducedLineMayerVietoris318.H1 (L' R S f c L)) :=
  OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c)
    (L' R S f c L) 1

/-- Actual global line H1 commutes with arbitrary coefficient extension,
using its independently defined structural action at BOTH ends. The
normalization is the original derived boundary and actual pullback units.
Identification with a separately constructed derived-functor base-change
natural transformation is a further compatibility theorem, not asserted here. -/
@[expose] def equivalence :
    S ⊗[R] NonreducedLineMayerVietoris318.H1 L ≃ₗ[S]
      NonreducedLineMayerVietoris318.H1 (L' R S f c L) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (ContactRelativeStructuralHOne318.equivalence R c L).symm).trans
      ((ContactCoefficientCechBaseChange318.equivalence R S f c L).trans
        (ContactRelativeStructuralHOne318.equivalence S c (L' R S f c L)))

lemma representative (s : S) (x : originalSections R c L) :
    equivalence R S f c L
      (s ⊗ₜ[R] ContactRelativeOriginalDerivedQuotient318.boundary R c L x) =
    ContactRelativeOriginalDerivedQuotient318.boundary S c (L' R S f c L)
      (s • ContactCoefficientLineCharts318.overlapRestriction R S f c L x) := by
  have hR : ContactRelativeStructuralHOne318.equivalence R c L
      ((ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ x) =
        ContactRelativeOriginalDerivedQuotient318.boundary R c L x :=
    ContactRelativeOriginalDerivedQuotient318.equivalence_mk R c L x
  change ContactRelativeStructuralHOne318.equivalence S c (L' R S f c L)
    (ContactCoefficientCechBaseChange318.equivalence R S f c L
      (s ⊗ₜ[R] (ContactRelativeStructuralHOne318.equivalence R c L).symm
        (ContactRelativeOriginalDerivedQuotient318.boundary R c L x))) = _
  rw [← hR,LinearEquiv.symm_apply_apply,ContactCoefficientCechBaseChange318.pure_tensor,
    overlap_pure]
  exact ContactRelativeOriginalDerivedQuotient318.equivalence_mk S c (L' R S f c L) _
end ContactOriginalHOneBaseChange318
