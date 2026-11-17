module
public import ActualTwoDescentNativeTensorMorphismProducts318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapNativeProduct318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalInverseInfinityTransition318 ActualTwoDescentOriginalOverlapSquareSections318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentNativeTensorMorphismProducts318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineProduct (n : K) (i : Fin 3) := product (affineValue n i) (affineValue n i)
def infinityProduct (n : K) (i : Fin 3) := product (infinityValue n i) (infinityValue n i)

/-- Full equality of native tensor morphisms on the ACTUAL common
chart,produced from the original pullback matching and literal pole unit. -/
lemma actual_overlap_product (n : K) (i : Fin 3) :
    affineProduct n i=infinityProduct n i ≫
      ClutchedModule318.multiply (rootSection n i*infinityCoefficient n i) := by
  apply hom_ext_pure
  intro U s t
  change (product (affineValue n i) (affineValue n i)).app U _=
    (ClutchedModule318.multiply _).app U ((product (infinityValue n i) (infinityValue n i)).app U _)
  rw [product_pure,product_pure,actual_overlap_values_apply,actual_overlap_values_apply,
    ClutchedModule318.multiply_apply,actual_section_square,map_pow]
  ring
end ActualTwoDescentOriginalOverlapNativeProduct318
