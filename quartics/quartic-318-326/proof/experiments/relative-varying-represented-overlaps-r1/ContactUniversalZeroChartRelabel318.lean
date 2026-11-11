module
public import ContactUniversalChartRelabel318
public import ContactUniversalSectionZeros318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace ContactUniversalZeroChartRelabel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactOriginalSectionParameter318
open ContactUniversalChartRelabel318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local notation "S" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl

abbrev finiteTensorRing := OriginalCoefficientTensor318.pushout (CommRingCat.of ℚ) R S
  (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)
abbrev infinityTensorRing := OriginalCoefficientTensor318.pushout (CommRingCat.of ℚ) R S
  (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)

abbrev finiteTensorLine := OriginalAffineComposedSection318.intermediate
  (CommRingCat.of (R ⊗[ℚ] finiteRing c)) (finiteTensorRing R c L)
  (OriginalCoefficientTensorSection318.inclusion (CommRingCat.of ℚ) R S
    (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)) (finiteLine R c L)
abbrev infinityTensorLine := OriginalAffineComposedSection318.intermediate
  (CommRingCat.of (R ⊗[ℚ] infinityRing c)) (infinityTensorRing R c L)
  (OriginalCoefficientTensorSection318.inclusion (CommRingCat.of ℚ) R S
    (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)) (infinityLine R c L)

@[expose] def finiteTensorIdeal := OriginalAffineSectionZero318.ideal (finiteTensorRing R c L)
  (finiteTensorLine R c L) (finiteTensorSection R c L hz)
@[expose] def infinityTensorIdeal := OriginalAffineSectionZero318.ideal (infinityTensorRing R c L)
  (infinityTensorLine R c L) (infinityTensorSection R c L hz)

/-- Literal ideal of the SAME actual global universal zero family,
transported through canonical original chart cancellation. -/
lemma finite_ideal : ContactOriginalSectionZeros318.finiteIdeal S c (universalLine R c L)
    (universalSection R c L hz) = Ideal.map
      (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
        (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)).toRingHom
      (finiteTensorIdeal R c L hz) := by
  have hh := OriginalAffineSectionZero318.along_path
    (OriginalCoefficientTensorSection318.relabel (CommRingCat.of ℚ) R S
      (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L))
    (finiteTensorLine R c L) (finiteLine S c (universalLine R c L))
    (OriginalCoefficientTensorSection318.comparison (CommRingCat.of ℚ) R S
      (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)
      (finiteLine R c L) (finiteLine S c (universalLine R c L)) (finitePath R c L))
    (finiteTensorSection R c L hz)
  change OriginalAffineSectionZero318.ideal _ _
    (OriginalCoefficientTensorSection318.restriction (CommRingCat.of ℚ) R S
      (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)
      (finiteLine R c L) (finiteLine S c (universalLine R c L)) (finitePath R c L)
      (finiteTensorSection R c L hz)) = _ at hh
  rw [finite_section] at hh
  exact hh

lemma infinity_ideal : ContactOriginalSectionZeros318.infinityIdeal S c (universalLine R c L)
    (universalSection R c L hz) = Ideal.map
      (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
        (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)).toRingHom
      (infinityTensorIdeal R c L hz) := by
  have hh := OriginalAffineSectionZero318.along_path
    (OriginalCoefficientTensorSection318.relabel (CommRingCat.of ℚ) R S
      (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L))
    (infinityTensorLine R c L) (infinityLine S c (universalLine R c L))
    (OriginalCoefficientTensorSection318.comparison (CommRingCat.of ℚ) R S
      (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)
      (infinityLine R c L) (infinityLine S c (universalLine R c L)) (infinityPath R c L))
    (infinityTensorSection R c L hz)
  change OriginalAffineSectionZero318.ideal _ _
    (OriginalCoefficientTensorSection318.restriction (CommRingCat.of ℚ) R S
      (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)
      (infinityLine R c L) (infinityLine S c (universalLine R c L)) (infinityPath R c L)
      (infinityTensorSection R c L hz)) = _ at hh
  rw [infinity_section] at hh
  exact hh

/-- Quotient rings, not merely zero sets or reduced schemes, are identified. -/
@[expose] def finiteQuotientEquiv :
    finiteTensorRing R c L ⧸ finiteTensorIdeal R c L hz ≃+*
      (S ⊗[ℚ] finiteRing c) ⧸ ContactOriginalSectionZeros318.finiteIdeal S c
        (universalLine R c L) (universalSection R c L hz) :=
  Ideal.quotientEquiv _ _
    (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
      (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)).toRingEquiv
    (finite_ideal R c L hz)
@[expose] def infinityQuotientEquiv :
    infinityTensorRing R c L ⧸ infinityTensorIdeal R c L hz ≃+*
      (S ⊗[ℚ] infinityRing c) ⧸ ContactOriginalSectionZeros318.infinityIdeal S c
        (universalLine R c L) (universalSection R c L hz) :=
  Ideal.quotientEquiv _ _
    (OriginalCoefficientTensor318.ringEquivalence (CommRingCat.of ℚ) R S
      (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)).toRingEquiv
    (infinity_ideal R c L hz)

@[expose] def finiteZeroIso : ContactUniversalSectionZeros318.finiteZero R c L hz ≅
    Spec (CommRingCat.of (finiteTensorRing R c L ⧸ finiteTensorIdeal R c L hz)) :=
  Scheme.Spec.mapIso (finiteQuotientEquiv R c L hz).toCommRingCatIso.op
@[expose] def infinityZeroIso : ContactUniversalSectionZeros318.infinityZero R c L hz ≅
    Spec (CommRingCat.of (infinityTensorRing R c L ⧸ infinityTensorIdeal R c L hz)) :=
  Scheme.Spec.mapIso (infinityQuotientEquiv R c L hz).toCommRingCatIso.op
end ContactUniversalZeroChartRelabel318
