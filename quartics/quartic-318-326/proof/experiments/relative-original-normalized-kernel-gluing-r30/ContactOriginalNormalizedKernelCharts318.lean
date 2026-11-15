module
public import ProjectiveKernelPrincipalCartesian318
public import ProjectiveKernelNormalizedCover318
public import ContactArbitrarySectionParameter318
public section
noncomputable section
namespace ContactOriginalNormalizedKernelCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318 ContactOriginalSectionKernel318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2
local notation "P" => zeroTerm R c L
local notation "Q" => oneTerm R c L
local notation "d" => boundary R c L
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i : Fin F.size)
abbrev principalRing := ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
abbrev sliceRing := ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i
abbrev principal : Scheme := Spec (CommRingCat.of (principalRing R c L i))
abbrev slice : Scheme := Spec (CommRingCat.of (sliceRing R c L i))
/-- The SAME original arbitrary-line section parameter, not a parameter
for tensor H0 or a replacement positive-twist line. -/
abbrev into : principal R c L i ⟶ ContactArbitrarySectionParameter318.parameterScheme R c L :=
  ProjectiveKernelPrincipalCartesian318.into R P Q d i
instance open : IsOpenImmersion (into R c L i) := inferInstance
abbrev normalize : principal R c L i ⟶ slice R c L i :=
  ProjectiveKernelNormalizedLaurent318.projection R P Q d i
instance smooth : Smooth (normalize R c L i) := inferInstance
instance surjective : Surjective (normalize R c L i) := inferInstance
/-- An actual Laurent-product chart over an actual normalized affine
kernel slice for EVERY original line. No H1(L)=0 or projective H0 premise. -/
@[expose] def laurent : principalRing R c L i ≃ₐ[R] LaurentPolynomial (sliceRing R c L i) :=
  ProjectiveKernelNormalizedLaurent318.algebraEquiv R P Q d i
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤
/-- The produced local quotient on all original coefficient tests. -/
@[expose] def points : (principalRing R c L i →ₐ[R] S) ≃
    Sˣ × (sliceRing R c L i →ₐ[R] S) :=
  ProjectiveKernelNormalizedAlgebras318.points R P Q d i S
/-- The exact full differential kernel is retained in each principal
point, supplying the old arbitrary-line sections equivalence. -/
@[expose] def kernelPoint (a : principalRing R c L i →ₐ[R] S) :
    LinearMap.ker (d.baseChange S) :=
  ⟨ProjectiveSectionParameter318.points R P S
      ((a.comp (ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i)).comp
        (ProjectiveParameterPrincipalNormalization318.point R P i)),by
    apply (ProjectiveKernelEquations318.equations_iff R P Q d S _).mp
    intro φ
    exact (AlgebraEquationQuotientPoints318.points R _ _ S a).property φ⟩
lemma kernelPoint_original (a : principalRing R c L i →ₐ[R] S) :
    kernelPoint R c L i S f a=ProjectiveKernelParameter318.points R P Q d S
      (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)) := by
  apply Subtype.ext
  change ProjectiveSectionParameter318.points R P S
    ((a.comp (ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i)).comp
      (ProjectiveParameterPrincipalNormalization318.point R P i))=
    ProjectiveSectionParameter318.points R P S
      (a.comp ((ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i).comp
        (ProjectiveKernelParameter318.quotient R P Q d)))
  rw [ProjectiveKernelPrincipalCartesian318.intoAlgebra_comp] <;> rfl
@[expose] def section (a : principalRing R c L i →ₐ[R] S) :
    Γ((L' R S f c L).object,⊤) := sections R c L S f (kernelPoint R c L i S f a)
/-- The new chart section is literally the OLD arbitrary-line section
at the actual intoAlgebra point, not an abstract isomorphic kernel. -/
lemma section_original (a : principalRing R c L i →ₐ[R] S) : section R c L i S f a=
    ContactArbitrarySectionParameter318.points R c L S f
      (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)) :=
  congrArg (sections R c L S f) (kernelPoint_original R c L i S f a)
/-- Exact original finite-complex coordinate retained by the new chart. -/
lemma section_coordinate (a : principalRing R c L i →ₐ[R] S) :
    (ContactRelativeFiniteCohomologyModel318.hzero S c (L' R S f c L) (bound R c L)
      (section R c L i S f a)).val=
      ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L (bound R c L)
        (positive_vanishing R c L) (kernelPoint R c L i S f a).val :=
  sections_coordinate R c L S f (kernelPoint R c L i S f a)

end ContactOriginalNormalizedKernelCharts318
