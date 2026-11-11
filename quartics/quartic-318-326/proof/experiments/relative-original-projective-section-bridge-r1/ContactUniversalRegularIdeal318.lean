module
public import OriginalUniversalRegularIdeal318
public import ContactUniversalZeroChartRelabel318
public section
noncomputable section
namespace ContactUniversalRegularIdeal318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionParameter318 ContactOriginalCoefficientActions318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "S" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl

/-- The actual universal finite-chart ideal, not an auxiliary tensor
ideal, has a regular principal affine cover. Canonical tensor cancellation
is consumed at the ideal used by the SAME global zero scheme. -/
theorem finite_property (hg : Submodule.span (R ⊗[ℚ] finiteRing c)
    (Set.range (ContactPositiveChartEvaluation318.finiteRestriction R c L))=⊤) :
    OriginalRegularIdealCover318.Property (CommRingCat.of (S ⊗[ℚ] finiteRing c))
      (ContactOriginalSectionZeros318.finiteIdeal S c (universalLine R c L)
        (universalSection R c L hz)) := by
  apply OriginalRegularIdealCover318.equivalence
    (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
      (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)).toRingEquiv
    (ContactUniversalZeroChartRelabel318.finiteTensorIdeal R c L hz) _
    (ContactUniversalZeroChartRelabel318.finite_ideal R c L hz)
  exact OriginalUniversalRegularIdeal318.property R (CommRingCat.of (R ⊗[ℚ] finiteRing c))
    (finiteLine R c L) Γ(L.object,⊤)
    (ContactPositiveChartEvaluation318.finiteRestriction R c L) hg

/-- The reciprocal route keeps its own actual line, parameter chart,
section ideal and cancellation isomorphism. -/
theorem infinity_property (hg : Submodule.span (R ⊗[ℚ] infinityRing c)
    (Set.range (ContactPositiveChartEvaluation318.infinityRestriction R c L))=⊤) :
    OriginalRegularIdealCover318.Property (CommRingCat.of (S ⊗[ℚ] infinityRing c))
      (ContactOriginalSectionZeros318.infinityIdeal S c (universalLine R c L)
        (universalSection R c L hz)) := by
  apply OriginalRegularIdealCover318.equivalence
    (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
      (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)).toRingEquiv
    (ContactUniversalZeroChartRelabel318.infinityTensorIdeal R c L hz) _
    (ContactUniversalZeroChartRelabel318.infinity_ideal R c L hz)
  exact OriginalUniversalRegularIdeal318.property R (CommRingCat.of (R ⊗[ℚ] infinityRing c))
    (infinityLine R c L) Γ(L.object,⊤)
    (ContactPositiveChartEvaluation318.infinityRestriction R c L) hg
end ContactUniversalRegularIdeal318
