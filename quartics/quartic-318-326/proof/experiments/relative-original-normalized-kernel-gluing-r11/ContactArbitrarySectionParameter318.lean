module
public import ContactOriginalSectionKernel318
public import ProjectiveKernelFiniteEquations318
public section
noncomputable section
namespace ContactArbitrarySectionParameter318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactOriginalSectionKernel318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2

/-- An actual affine coefficient ring for sections of EVERY original line. Its
full linear ideal cuts out the kernel inside the positive-twist section parameter. -/
abbrev parameterRing := ProjectiveKernelParameter318.algebra R
  (zeroTerm R c L) (oneTerm R c L) (boundary R c L)
abbrev parameterScheme : Scheme := Spec (CommRingCat.of (parameterRing R c L))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) :=
  IsScalarTower.of_algebraMap_eq' rfl
@[expose] def parameterCoefficient : R →ₐ[ℚ] parameterRing R c L :=
  IsScalarTower.toAlgHom ℚ R (parameterRing R c L)
@[expose] def parameterProjection : parameterScheme R c L ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (parameterCoefficient R c L).toRingHom)

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

/-- Both inverse maps are present on ALL coefficient tests, including nonreduced
and nonflat extensions. This does not assert finite projectivity of H0(L). -/
@[expose] def points : (parameterRing R c L →ₐ[R] S) ≃ Γ((L' R S f c L).object,⊤) :=
  (ProjectiveKernelParameter318.points R (zeroTerm R c L) (oneTerm R c L)
    (boundary R c L) S).trans (sections R c L S f).toEquiv

/-- The universal point is a real global section of the actual pulled original line. -/
@[expose] def universalSection : Γ((L' R (CommRingCat.of (parameterRing R c L))
    (parameterCoefficient R c L) c L).object,⊤) :=
  points R c L (CommRingCat.of (parameterRing R c L))
    (parameterCoefficient R c L) (AlgHom.id R _)
end ContactArbitrarySectionParameter318
