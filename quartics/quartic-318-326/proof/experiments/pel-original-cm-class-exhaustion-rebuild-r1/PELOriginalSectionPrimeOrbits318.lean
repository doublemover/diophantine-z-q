module
public import PELOriginalSectionInvariantExtension318
public section
noncomputable section
namespace PELOriginalSectionPrimeOrbits318
open AlgebraicGeometry CategoryTheory
open scoped Pointwise
open PELOriginalWholeCharacterMorphisms318
open PELOriginalSectionKernelAction318 PELOriginalSectionInvariantExtension318

/-- Every pair of primes in the ACTUAL full-inverse-image section ring
with identical contraction to the actual target section ring is in one
original-kernel orbit. No maximality or Dedekind hypothesis is assumed. -/
theorem original_prime_transitive (i:Fin 4) (U:(Curve i).Opens)
    (P Q:Ideal (SourceSections i U)) [P.IsPrime] [Q.IsPrime]
    (hPQ:Ideal.comap ((morphism i).app U).hom P=
      Ideal.comap ((morphism i).app U).hom Q):
    letI:=sectionActionInstance i U
    letI:=sectionAlgebra i U
    ∃a:Kernel i,Q=a•P:=by
  letI:=sectionActionInstance i U
  letI:=sectionAlgebra i U
  letI:=sectionScalarComm i U
  letI:=sectionIsInvariant i U
  exact Algebra.IsInvariant.exists_smul_of_under_eq
    (BaseSections i U) (SourceSections i U) (Kernel i) P Q hPQ

/-- The actual section algebra is integral over the target section
algebra by its FINITE original kernel action and produced invariant
image. This assertion holds on every open, not only affine opens. -/
theorem original_section_integral (i:Fin 4) (U:(Curve i).Opens):
    letI:=sectionAlgebra i U
    Algebra.IsIntegral (BaseSections i U) (SourceSections i U):=by
  letI:=sectionAlgebra i U
  letI:=sectionActionInstance i U
  letI:=sectionIsInvariant i U
  exact Algebra.IsInvariant.isIntegral
    (BaseSections i U) (SourceSections i U) (Kernel i)
end PELOriginalSectionPrimeOrbits318
