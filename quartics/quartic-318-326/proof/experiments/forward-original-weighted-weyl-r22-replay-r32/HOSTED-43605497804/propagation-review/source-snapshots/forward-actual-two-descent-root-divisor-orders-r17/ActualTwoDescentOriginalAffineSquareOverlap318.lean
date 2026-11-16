module
public import ActualTwoDescentOriginalAffineRootSectionPullback318
public section
noncomputable section
namespace ActualTwoDescentOriginalAffineSquareOverlap318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalRootOverlapRefinement318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalRootNativeSquareCharts318
open ActualTwoDescentOriginalNativeSquareProduct318 ActualTwoDescentOriginalAffineOverlapInclusion318
open ActualTwoDescentOriginalAffineRootSectionPullback318 ActualTwoDescentOriginalOverlapSquareSections318
open ActualTwoDescentNativeOpenRefinementValues318 ActualTwoDescentNativeTensorRestrictionProducts318
open ActualTwoDescentNativeTensorMorphismProducts318 ActualTwoDescentOriginalMatchedSquareIsomorphisms318
open ActualTwoDescentOriginalMatchedTensorSquare318 ActualTwoDescentOriginalOverlapNativeProduct318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineSquareOnOverlap (n : K) (i : Fin 3) (b : Bool) :
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)).restrict
      (overlapEmbedding n) ⟶ SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  value (intoRootChart n i b) (rootLocalizationMorphism n i b ≫ affineChart n)
    (overlapEmbedding n) (actual_root_overlap_ambient n i b)
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i))
    (affineSquareChart n i b).hom

/-- Every subopen of the complete overlap,using the ACTUAL old affine
square and old inclusion. The root is inverted only after reaching this chart. -/
lemma actual_refined_affine_square_product (n : K) (i : Fin 3) (b : Bool)
    (U : (overlapScheme n).Opens) (s t : Γ(overlapIdeal n i,U)) :
    ((overlapScheme n).presheaf.map (homOfLE (show U≤⊤ from le_top)).op (rootSection n i))*
      (affineSquareOnOverlap n i b).app U
        (IntrinsicTensorSheaf318.pure (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)
          ((overlapEmbedding n) ''ᵁ U) s t)=
    (ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i).app U s*
      (ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i).app U t := by
  have hh := value_square_product (intoRootChart n i b)
    (rootLocalizationMorphism n i b ≫ affineChart n) (overlapEmbedding n)
    (actual_root_overlap_ambient n i b) (originalRootIdealSheaf n i)
    (ActualTwoDescentOriginalAffineInclusionFrame318.affineValue n i b)
    (affineSquareChart n i b).hom (principalRootSection n i b)
    (fun V s t => actual_affine_square_product n i b V s t) U s t
  rw [actual_principal_root_pullback] at hh
  change _=(affineValueOnOverlap n i b).app U s*(affineValueOnOverlap n i b).app U t at hh
  simp only [actual_principal_value_matches] at hh
  exact hh

/-- Both old affine square restrictions are EXACTLY the previously
matched native square. Cancellation uses the produced unit on this entire
common chart and nowhere on a root-containing affine chart. -/
lemma actual_old_affine_square_matches (n : K) (i : Fin 3) (b : Bool) :
    affineSquareOnOverlap n i b=(matchedSquareIso n i).hom := by
  rw [actual_matched_square_affine]
  apply hom_ext_restricted
  intro U s t
  let r : Γ(overlapScheme n,⊤) →+* Γ(overlapScheme n,U) :=
    ((overlapScheme n).presheaf.map (homOfLE (show U≤⊤ from le_top)).op).hom
  let u : Γ(overlapScheme n,U)ˣ := Units.map r.toMonoidHom (rootSectionUnit n i)
  have h := actual_refined_affine_square_product n i b U s t
  rw [←rootSectionUnit_value] at h
  change (u : Γ(overlapScheme n,U))*
    (affineSquareOnOverlap n i b).app U
      (IntrinsicTensorSheaf318.pure (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)
        ((overlapEmbedding n) ''ᵁ U) s t)=_ at h
  change (affineSquareOnOverlap n i b).app U _=
    (affineSquare n i).app U
      ((TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
        (originalRootIdealSheaf n i)).hom.app U _)
  rw [TensorSheafNormalization318.restriction_pure]
  change _=(ClutchedModule318.multiply ((rootSectionUnit n i)⁻¹ : Γ(overlapScheme n,⊤)ˣ)).app U
    ((product (ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i)
      (ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i)).app U _)
  rw [product_pure,ClutchedModule318.multiply_apply]
  change _=((ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i).app U s*
    (ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i).app U t)*(↑(u⁻¹))
  calc
    _ = (↑(u⁻¹))*((u : Γ(overlapScheme n,U))*
      (affineSquareOnOverlap n i b).app U _) := by rw [←mul_assoc,Units.inv_mul,one_mul]
    _ = _ := by rw [h,mul_comm]
end ActualTwoDescentOriginalAffineSquareOverlap318
