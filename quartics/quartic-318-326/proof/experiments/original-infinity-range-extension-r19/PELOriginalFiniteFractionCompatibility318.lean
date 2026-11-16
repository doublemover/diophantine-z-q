module
public import PELOriginalFiniteFunctionRange318
public import PELOriginalCoordinateFractionField318
public section
noncomputable section
namespace PELOriginalFiniteFractionCompatibility318
open PELOriginalRegularCoordinateAlgebra318 PELOriginalCoordinateRangeDeck318
open PELOriginalCompletedChartEvaluation318 PELOriginalFiniteFunctionRange318

/-- The full finite-chart algebra has the same faithful original coordinate
presentation, not an arbitrary field chosen from its dimension. -/
lemma finiteCoefficientMap_injective :
    Function.Injective PELOriginalFiniteFunctionRange318.coefficientMap := by
  intro a b h
  apply finiteEvaluation_injective
  exact congrArg Subtype.val h

@[expose] def finiteCoordinateEquiv : CoordinateRing ≃ₐ[ℂ] FiniteAlgebra :=
  AlgEquiv.ofBijective PELOriginalFiniteFunctionRange318.coefficientMap
    ⟨finiteCoefficientMap_injective,coefficientMap_surjective⟩

/-- Restriction of each full finite coordinate function is the identical
original regular function, not merely an isomorphic algebra element. -/
lemma restriction_coordinate (a : CoordinateRing) :
    restrictionEquiv (finiteCoordinateEquiv a) =
      PELOriginalCoordinateFractionField318.coordinateEquiv a := by
  apply Subtype.ext
  funext x
  exact regular_evaluation a x

/-- Domain structure is transported from the already constructed original
regular range through literal restriction, not from the ambient function ring. -/
instance finiteDomain : IsDomain FiniteAlgebra :=
  Function.Injective.isDomain restrictionEquiv restrictionEquiv.injective

abbrev FiniteFractionField := FractionRing FiniteAlgebra

/-- Extend the ACTUAL finite-to-regular restriction, uniquely, to the
fraction fields of these two original function algebras. -/
@[expose] def fractionRestriction :
    FiniteFractionField ≃+* PELOriginalCoordinateFractionField318.CoordinateFractionField :=
  IsFractionRing.ringEquivOfRingEquiv restrictionEquiv.toRingEquiv

lemma fractionRestriction_coefficient (a : FiniteAlgebra) :
    fractionRestriction (algebraMap FiniteAlgebra FiniteFractionField a) =
      algebraMap OriginalAlgebra PELOriginalCoordinateFractionField318.CoordinateFractionField
        (restrictionEquiv a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap restrictionEquiv.toRingEquiv a

/-- The commuting square retains every original coordinate-ring element,
not only its base coordinate or a finite test set. -/
lemma fractionRestriction_original (a : CoordinateRing) :
    fractionRestriction (algebraMap FiniteAlgebra FiniteFractionField
      (finiteCoordinateEquiv a)) = PELOriginalCoordinateFractionField318.fractionMap a := by
  rw [fractionRestriction_coefficient,restriction_coordinate]
  rfl

/-- Constants retain their original complex value. This identifies only
the coordinate-function fraction algebras, not the full meromorphic field. -/
lemma fractionRestriction_complex_scalar (c : ℂ) :
    fractionRestriction (algebraMap FiniteAlgebra FiniteFractionField
      (algebraMap ℂ FiniteAlgebra c)) =
      algebraMap OriginalAlgebra PELOriginalCoordinateFractionField318.CoordinateFractionField
        (algebraMap ℂ OriginalAlgebra c) := by
  rw [fractionRestriction_coefficient,restrictionEquiv.commutes]
end PELOriginalFiniteFractionCompatibility318
