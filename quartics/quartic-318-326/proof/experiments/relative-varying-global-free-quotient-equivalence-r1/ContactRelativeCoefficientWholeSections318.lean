module
public import OriginalOpenCoefficientSections318
public import ContactRelativeCechProjective318
public section
noncomputable section
namespace ContactRelativeCoefficientWholeSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeWholeOpenSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance (U : (curve R c).Opens) : Module R Γ(L.object,U) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L U

@[expose] def finiteEquivalence : finiteSections R c L ≃ₗ[R] Γ(L.object,finiteOpen R c) :=
  (finiteIdentity R c L).trans
    (OriginalOpenCoefficientSections318.equivalence R (CommRingCat.of (R ⊗[ℚ] finiteRing c))
      (ContactRelativeStructuralHOne318.projection R c) (finiteInto R c)
      (CommRingCat.ofHom (algebraMap R (R ⊗[ℚ] finiteRing c)))
      (RelativeOriginalAffineChart318.over_test (CommRingCat.of ℚ) R (finiteRing c)
        (ContactOriginalAffineTestCover318.p c) (SourceGlobalAffine318.chartEmbedding c)
        (ContactOriginalRelativePolynomialCharts318.finite_over c)) L)

@[expose] def infinityEquivalence : infinitySections R c L ≃ₗ[R] Γ(L.object,infinityOpen R c) :=
  (infinityIdentity R c L).trans
    (OriginalOpenCoefficientSections318.equivalence R (CommRingCat.of (R ⊗[ℚ] infinityRing c))
      (ContactRelativeStructuralHOne318.projection R c) (infinityInto R c)
      (CommRingCat.ofHom (algebraMap R (R ⊗[ℚ] infinityRing c)))
      (RelativeOriginalAffineChart318.over_test (CommRingCat.of ℚ) R (infinityRing c)
        (ContactOriginalAffineTestCover318.p c) (ContactWholeInfinityScheme318.into c)
        (ContactOriginalRelativePolynomialCharts318.infinity_over c)) L)

@[expose] def overlapEquivalence : originalSections R c L ≃ₗ[R]
    Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) where
  __ := ContactRelativeWholeOpenSections318.overlapEquiv R c L
  map_smul' := ContactRelativeStructuralHOne318.overlap_scalar R c L
end ContactRelativeCoefficientWholeSections318
