module
public import ContactArbitrarySectionParameter318
public section
noncomputable section
namespace ContactArbitrarySectionSpecialization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactOriginalSectionKernel318 ContactArbitrarySectionParameter318
open scoped TensorProduct
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
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

/-- Every actual original section is obtained from the SAME universal kernel
by literal algebra specialization and the genuine original cohomology comparison.
Native geometric pullback of the universal section requires its own composition square. -/
lemma specialize (a : parameterRing R c L →ₐ[R] S) :
    sections R c L S f
      (ProjectiveKernelNaturality318.transport R (zeroTerm R c L) (oneTerm R c L)
        (boundary R c L) (parameterRing R c L) a
        (ProjectiveKernelNaturality318.universal R (zeroTerm R c L) (oneTerm R c L)
          (boundary R c L))) = points R c L S f a := by
  rw [ProjectiveKernelNaturality318.specialize]
  rfl

/-- The equations defining the actual parameter are finite, using a projective
frame of the original jet module, never an assumed basis. -/
lemma finite_equations : ProjectiveKernelParameter318.ideal R
    (zeroTerm R c L) (oneTerm R c L) (boundary R c L) =
    Ideal.span (Set.range (fun i : Fin (FiniteProjectiveEvaluationFrame318.frame R
      (oneTerm R c L)).size => ProjectiveKernelEquations318.equation R
        (zeroTerm R c L) (oneTerm R c L) (boundary R c L)
        ((FiniteProjectiveEvaluationFrame318.frame R (oneTerm R c L)).coordinate i))) :=
  ProjectiveKernelFiniteEquations318.finite_equations R _ _ _
    (FiniteProjectiveEvaluationFrame318.frame R (oneTerm R c L))

lemma recover (s : Γ((L' R S f c L).object,⊤)) :
    points R c L S f ((points R c L S f).symm s)=s :=
  (points R c L S f).apply_symm_apply s
end ContactArbitrarySectionSpecialization318
