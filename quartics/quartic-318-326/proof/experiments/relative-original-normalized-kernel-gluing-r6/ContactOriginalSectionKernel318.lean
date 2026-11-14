module
public import ContactFiniteComplexCoefficient318
public import ProjectiveKernelNaturality318
public section
noncomputable section
namespace ContactOriginalSectionKernel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeGeometricTwist318 ContactRelativeFiniteCohomologyModel318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤

/-- Only a positive twist is made acyclic; the original line is arbitrary. -/
@[expose] def bound : ℕ := (exists_model R c L).choose
lemma positive_vanishing : ∀ x : NonreducedLineMayerVietoris318.H1
    (twist R c L ((bound R c L+1 : ℕ) : ℤ)),x=0 :=
  (exists_model R c L).choose_spec.1

abbrev zeroTerm := termZero R c L (bound R c L)
abbrev oneTerm := termOne R c L (bound R c L)
abbrev boundary := differential R c L (bound R c L)

lemma projective_terms :
    (Module.Finite R (zeroTerm R c L) ∧ Module.Projective R (zeroTerm R c L)) ∧
    (Module.Finite R (oneTerm R c L) ∧ Module.Projective R (oneTerm R c L)) :=
  (exists_model R c L).choose_spec.2

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

/-- The kernel of the ACTUAL base-changed finite-projective differential is exactly
sections of the literal pulled original line. Neither flatness of R→S nor H1(L)=0
is assumed, and tensoring H0(L) is not substituted for this kernel. -/
@[expose] def sections : LinearMap.ker ((boundary R c L).baseChange S) ≃ₗ[S]
    Γ((L' R S f c L).object,⊤) :=
  (KernelComparisonTransport318.equivalence ((boundary R c L).baseChange S)
    (differential S c (L' R S f c L) (bound R c L))
    (ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L (bound R c L)
      (positive_vanishing R c L))
    (ContactFiniteComplexCoefficient318.oneEquivalence R S f c L (bound R c L))
    (ContactFiniteComplexCoefficient318.differential_square R S f c L (bound R c L)
      (positive_vanishing R c L))).trans
    (hzero S c (L' R S f c L) (bound R c L)).symm

/-- The comparison retains the actual original finite-complex inclusion, not just
an abstract cardinality or module-isomorphism witness. -/
lemma sections_coordinate (x : LinearMap.ker ((boundary R c L).baseChange S)) :
    (hzero S c (L' R S f c L) (bound R c L) (sections R c L S f x)).val =
      ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L (bound R c L)
        (positive_vanishing R c L) x.val := by
  change ((hzero S c (L' R S f c L) (bound R c L))
    ((hzero S c (L' R S f c L) (bound R c L)).symm _)).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl
end ContactOriginalSectionKernel318
