module
public import ActualTwoDescentOriginalGenericFunctionsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllStalkFractionsRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual common generic field is a fraction field of EVERY
original scheme stalk, including non-rational points. -/
theorem all_stalk_fraction (n : K) (p : originalCubicScheme n) :
    IsFractionRing ((originalCubicScheme n).presheaf.stalk p)
      (originalCubicScheme n).functionField := inferInstance

theorem all_stalk_injective (n : K) (p : originalCubicScheme n) :
    Function.Injective (algebraMap ((originalCubicScheme n).presheaf.stalk p)
      (originalCubicScheme n).functionField) :=
  IsFractionRing.injective _ _

theorem actual_section_square (n : K) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (p : originalCubicScheme n) (hp : p ∈ U)
    (s : Γ(originalCubicScheme n,U)) :
    algebraMap ((originalCubicScheme n).presheaf.stalk p)
      (originalCubicScheme n).functionField
      ((originalCubicScheme n).presheaf.germ U p hp s) =
        (originalCubicScheme n).germToFunctionField U s :=
  Scheme.algebraMap_germ_eq_germToFunctionField hp s
end ActualTwoDescentOriginalAllStalkFractionsRebuild318
