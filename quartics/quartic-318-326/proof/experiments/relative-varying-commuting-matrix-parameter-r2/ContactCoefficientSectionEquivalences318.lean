module
public import OriginalCoefficientSections318
public import ContactCoefficientLineCharts318
public section
noncomputable section
namespace ContactCoefficientSectionEquivalences318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (ContactOriginalRelativeLineOverlap318.originalSections R c L) :=
  Module.compHom _ (algebraMap R (ring R c))

/-- Coefficient-only section base change on the exact whole finite chart. -/
abbrev finiteEquivalence := OriginalCoefficientSections318.equivalence
  (CommRingCat.of ℚ) R S (finiteRing c) f (ContactOriginalAffineTestCover318.p c)
  (SourceGlobalAffine318.chartEmbedding c) (finite_over c) L
/-- Coefficient-only section base change on the distinct whole infinity chart. -/
abbrev infinityEquivalence := OriginalCoefficientSections318.equivalence
  (CommRingCat.of ℚ) R S (infinityRing c) f (ContactOriginalAffineTestCover318.p c)
  (ContactWholeInfinityScheme318.into c) (infinity_over c) L
/-- Coefficient-only section base change on the same complete common overlap. -/
abbrev overlapEquivalence := OriginalCoefficientSections318.equivalence
  (CommRingCat.of ℚ) R S (oldRing c) f (ContactOriginalAffineTestCover318.p c)
  (oldInto c) (old_over c) L

/-- The overlap comparison is pinned to the genuine original pullback
unit. Thus its normalization cannot be silently changed before H1. -/
lemma overlap_unit (m : ContactOriginalRelativeLineOverlap318.originalSections R c L) :
    overlapEquivalence R S f c L ((1 : S) ⊗ₜ[R] m) =
      ContactCoefficientLineCharts318.overlapRestriction R S f c L m :=
  OriginalCoefficientSections318.unit _ _ _ _ _ _ _ _ _ m
end ContactCoefficientSectionEquivalences318
