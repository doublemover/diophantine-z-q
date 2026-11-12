module
public import ActualTwoDescentOpenAffineCoefficientSquareRebuild318
public import AffineFunctionFieldMap318
public section
noncomputable section
namespace ActualTwoDescentOpenChartCoefficientRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} [IsIntegral X] {R : Type u} [CommRing R] [IsDomain R]
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

/-- Literal affine coefficients in the SAME native generic stalk. -/
def coefficient : R →+* X.functionField :=
  (OpenFunctionField318.fieldEquiv j).symm.toRingHom.comp
    (algebraMap R (Spec (CommRingCat.of R)).functionField)

lemma comparison (r : R) :
    OpenFunctionField318.fieldEquiv j (coefficient j r)=
      algebraMap R (Spec (CommRingCat.of R)).functionField r :=
  (OpenFunctionField318.fieldEquiv j).apply_symm_apply _

lemma fraction_comparison (r : R) :
    OpenFunctionField318.openFractionEquiv j (coefficient j r)=
      algebraMap R (FractionRing R) r := by
  change OpenFunctionField318.affineFractionEquiv (CommRingCat.of R)
    (OpenFunctionField318.fieldEquiv j (coefficient j r))=_
  rw [comparison]
  exact (OpenFunctionField318.affineFractionEquiv (CommRingCat.of R)).commutes r

lemma injective : Function.Injective (coefficient j) := by
  intro r s h
  apply IsFractionRing.injective R (FractionRing R)
  simpa only [fraction_comparison] using congrArg (OpenFunctionField318.openFractionEquiv j) h

lemma stalk_square (p : PrimeSpectrum R) (r : R) :
    algebraMap (X.presheaf.stalk (j p)) X.functionField
      (ActualTwoDescentOpenAffineStalkRebuild318.coefficient j p r)=coefficient j r := by
  apply (OpenFunctionField318.fieldEquiv j).injective
  rw [comparison]
  exact ActualTwoDescentOpenAffineCoefficientSquareRebuild318.generic_square j p r
end ActualTwoDescentOpenChartCoefficientRebuild318
