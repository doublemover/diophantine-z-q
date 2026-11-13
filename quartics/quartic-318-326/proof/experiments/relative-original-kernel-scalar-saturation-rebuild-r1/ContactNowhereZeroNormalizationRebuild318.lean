module
public import ContactNowhereZeroSourceTestsRebuild318
public section
noncomputable section
namespace ContactNowhereZeroNormalizationRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
/-- Restrict the genuine original normalization to the WHOLE original
nowhere-zero open. No target-open saturation/effectivity is built into it. -/
def map : ContactArbitraryNowhereZeroOpen318.scheme R c L ⟶
    ContactOriginalNormalizedKernelScheme318.scheme R c L :=
  ContactNowhereZeroSourceOpenRebuild318.inclusion R c L ≫
    ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L
instance smooth : Smooth (map R c L) := by
  dsimp only [map]
  infer_instance
instance flat : Flat (map R c L) := inferInstance
instance locallyOfFinitePresentation : LocallyOfFinitePresentation (map R c L) := inferInstance
/-- The map retains the literal original coefficient morphism. -/
@[reassoc] lemma coefficient : map R c L ≫
    ContactOriginalNormalizedKernelScheme318.projection R c L =
      ContactArbitraryNowhereZeroOpen318.into R c L ≫ parameterProjection R c L := by
  dsimp only [map]
  rw [Category.assoc,ContactOriginalGlobalKernelNormalizationRebuild318.coefficient,
    ← Category.assoc,ContactNowhereZeroSourceOpenRebuild318.original] <;> rfl
/-- Every residue test recovers its earlier literal normalized field lift. -/
@[reassoc] lemma residue (y : ContactArbitraryNowhereZeroOpen318.scheme R c L) :
    (ContactArbitraryNowhereZeroOpen318.scheme R c L).fromSpecResidueField y ≫ map R c L =
      (ContactNowhereZeroResidueSourceRebuild318.data R c L y).val ≫
        ContactOriginalGlobalKernelNormalizationRebuild318.normalize R c L := by
  dsimp only [map]
  rw [← Category.assoc,ContactNowhereZeroSourceOpenRebuild318.residue]
end ContactNowhereZeroNormalizationRebuild318
