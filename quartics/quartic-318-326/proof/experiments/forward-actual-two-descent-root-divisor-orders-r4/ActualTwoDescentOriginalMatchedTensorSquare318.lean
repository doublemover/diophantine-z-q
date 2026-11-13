module
public import ActualTwoDescentOriginalOverlapNativeProduct318
public section
noncomputable section
namespace ActualTwoDescentOriginalMatchedTensorSquare318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalInverseInfinityTransition318 ActualTwoDescentOriginalOverlapSquareSections318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentNativeTensorMorphismProducts318
open ActualTwoDescentOriginalOverlapNativeProduct318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineSquare (n : K) (i : Fin 3) := affineProduct n i ≫
  ClutchedModule318.multiply (((rootSectionUnit n i)⁻¹ : Γ(overlapScheme n,⊤)ˣ) : Γ(overlapScheme n,⊤))
def infinitySquare (n : K) (i : Fin 3) := infinityProduct n i ≫
  ClutchedModule318.multiply (infinityCoefficient n i)

/-- The two exact normalized square maps MATCH on the complete
common chart. No compatibility premise,no generic-field injection and no
replacement of the actual global ideal or its actual projections. -/
lemma actual_square_maps_match (n : K) (i : Fin 3) : affineSquare n i=infinitySquare n i := by
  apply hom_ext_pure
  intro U s t
  change (ClutchedModule318.multiply _).app U ((product (affineValue n i) (affineValue n i)).app U _)=
    (ClutchedModule318.multiply _).app U ((product (infinityValue n i) (infinityValue n i)).app U _)
  rw [product_pure,product_pure,actual_overlap_values_apply,actual_overlap_values_apply,
    ClutchedModule318.multiply_apply,ClutchedModule318.multiply_apply]
  let r := ((overlapScheme n).presheaf.map (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op).hom
  have h := congrArg r (actual_inverse_section_square n i)
  rw [map_mul,map_pow] at h
  change (((infinityValue n i).app U s*r (inverseUSection n))*
    ((infinityValue n i).app U t*r (inverseUSection n)))*
      r (((rootSectionUnit n i)⁻¹ : Γ(overlapScheme n,⊤)ˣ) : Γ(overlapScheme n,⊤))=
    ((infinityValue n i).app U s*(infinityValue n i).app U t)*r (infinityCoefficient n i)
  linear_combination (infinityValue n i).app U s*(infinityValue n i).app U t*h

/-- The same matching is consumed on the RESTRICTION of the native
tensor square of the original GLOBAL ideal sheaf via its actual native
restriction comparison. Identification with each old chart's restricted
square frame,and global gluing,are still separate next steps. -/
lemma actual_global_tensor_overlap_match (n : K) (i : Fin 3) :
    (TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
      (originalRootIdealSheaf n i)).hom ≫ affineSquare n i=
    (TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
      (originalRootIdealSheaf n i)).hom ≫ infinitySquare n i := by
  rw [actual_square_maps_match]
end ActualTwoDescentOriginalMatchedTensorSquare318
