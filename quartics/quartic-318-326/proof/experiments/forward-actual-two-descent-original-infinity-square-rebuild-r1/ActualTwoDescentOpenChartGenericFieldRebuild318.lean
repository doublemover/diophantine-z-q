module
public import ActualTwoDescentOriginalIntegralSchemeRebuild318
public import OpenFunctionField318
public section
noncomputable section
namespace ActualTwoDescentOpenChartGenericFieldRebuild318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : X ⟶ Y) [IsOpenImmersion j]

/-- Reuse the surviving exact native open-immersion generic-stalk
comparison, including its Inseparable equality transport. -/
def comparison : Y.functionField ≃+* X.functionField :=
  OpenFunctionField318.fieldEquiv j

/-- The same native comparison commutes with EVERY actual section germ. -/
lemma section_square (U : Y.Opens) [Nonempty U] [Nonempty (j ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ (OpenFunctionField318.fieldIso j).hom =
      j.app U ≫ X.germToFunctionField (j ⁻¹ᵁ U) :=
  OpenFunctionField318.fieldIso_germ j U

variable {R : Type u} [CommRing R] [IsDomain R]
    (f : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion f]

/-- Native localization uniqueness over the SAME affine coordinate ring. -/
def fractionComparison : Y.functionField ≃+* FractionRing R :=
  OpenFunctionField318.openFractionEquiv f

lemma comparison_injective : Function.Injective (fractionComparison f) :=
  (fractionComparison f).injective
lemma comparison_surjective : Function.Surjective (fractionComparison f) :=
  (fractionComparison f).surjective
end ActualTwoDescentOpenChartGenericFieldRebuild318
