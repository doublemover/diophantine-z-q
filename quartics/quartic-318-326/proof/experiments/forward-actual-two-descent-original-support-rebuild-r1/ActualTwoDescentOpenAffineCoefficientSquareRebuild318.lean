module
public import ActualTwoDescentOpenStalkGenericSquareRebuild318
public section
noncomputable section
namespace ActualTwoDescentOpenAffineCoefficientSquareRebuild318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ActualTwoDescentOpenAffineStalkRebuild318
universe u
variable {X : Scheme.{u}} [IsIntegral X] {R : Type u} [CommRing R] [IsDomain R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum R)

/-- The coordinate chosen by the actual local equivalence is exactly
the native affine coordinate germ after applying j.stalkMap. -/
lemma local_square (r : R) :
    j.stalkMap p (coefficient j p r) = StructureSheaf.toStalk R p r := by
  apply (Spec.stalkIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv.injective
  change equivalence j p (coefficient j p r) =
    (StructureSheaf.stalkIso R p) (StructureSheaf.toStalk R p r)
  rw [coefficient_image]
  exact ((StructureSheaf.stalkIso R p).commutes r).symm

lemma generic_square (r : R) :
    OpenFunctionField318.fieldEquiv j
      (algebraMap (X.presheaf.stalk (j p)) X.functionField (coefficient j p r)) =
        algebraMap R (Spec (CommRingCat.of R)).functionField r := by
  rw [ActualTwoDescentOpenStalkGenericSquareRebuild318.square_apply, local_square]
  exact congrArg (fun f => f r)
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (CommRingCat.of R))).specializes (Set.mem_univ p)))

/-- Exact coefficient preservation in the SAME original affine fraction
field, not only an abstract equivalence of fields. -/
lemma fraction_square (r : R) :
    ActualTwoDescentOpenChartGenericFieldRebuild318.fractionComparison j
      (algebraMap (X.presheaf.stalk (j p)) X.functionField (coefficient j p r)) =
        algebraMap R (FractionRing R) r := by
  change OpenFunctionField318.affineFractionEquiv (CommRingCat.of R)
    (OpenFunctionField318.fieldEquiv j
      (algebraMap (X.presheaf.stalk (j p)) X.functionField (coefficient j p r))) = _
  rw [generic_square]
  exact (OpenFunctionField318.affineFractionEquiv (CommRingCat.of R)).commutes r
end ActualTwoDescentOpenAffineCoefficientSquareRebuild318
