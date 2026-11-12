module
public import LegendreHalfPlaneAnalyticSheets318
public import PELOriginalCommonLegendreBase318
public import PELOriginalRealBranchParameters318
public section
noncomputable section
namespace PELOriginalLegendreAnalyticSheets318
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalCommonLegendreBase318
open scoped OnePoint

/-- The concrete Legendre model for the SAME original character branch
parameter now has two analytic, distinct, exhaustive halfplane sheets. -/
theorem original_target_sheets (i:Fin 4) (upper:Bool) :
    AnalyticOnNhd ℂ (fun z=>(positivePoint (branchParameter i)
      (branchParameter_im_zero i) upper z).val) (domain upper) ∧
    AnalyticOnNhd ℂ (fun z=>(negativePoint (branchParameter i)
      (branchParameter_im_zero i) upper z).val) (domain upper) ∧
    ∀p:FinitePoints (branchParameter i),p.val.1∈domain upper→
      (p=positivePoint (branchParameter i) (branchParameter_im_zero i) upper p.val.1 ∨
       p=negativePoint (branchParameter i) (branchParameter_im_zero i) upper p.val.1) ∧
      negativePoint (branchParameter i) (branchParameter_im_zero i) upper p.val.1≠
        positivePoint (branchParameter i) (branchParameter_im_zero i) upper p.val.1 :=
  ⟨positive_coordinates_analytic _ _ _,negative_coordinates_analytic _ _ _,
    sheet_exhaustion _ _ _⟩

/-- Both actual target sheets project to the actual original base point.
There is still NO claimed choice between them for an original source point;
that requires the covering lift and compatibility across branch cuts. -/
theorem exact_original_base (i:Fin 4) (upper:Bool) (x:CharacterBase i) (z:ℂ)
    (hz:normalizedMap i x=(z:OnePoint ℂ)) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (some (positivePoint (branchParameter i)
        (branchParameter_im_zero i) upper z)))=originalProjection i x ∧
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (some (negativePoint (branchParameter i)
        (branchParameter_im_zero i) upper z)))=originalProjection i x := by
  rw [original_projection_coordinate,hz]
  exact original_scheme_sections _ _ _ _
end PELOriginalLegendreAnalyticSheets318
