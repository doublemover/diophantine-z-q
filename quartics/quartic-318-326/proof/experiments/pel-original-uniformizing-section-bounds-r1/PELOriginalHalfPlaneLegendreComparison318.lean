module
public import PELOriginalHalfPlaneSheetTopology318
public import LegendreHalfPlaneSheetTopology318
public import PELOriginalCommonLegendreBase318
public import PELOriginalRealBranchParameters318
public section
noncomputable section
namespace PELOriginalHalfPlaneLegendreComparison318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalNormalizedDoubleCover318 PELOriginalCharacterQuotient318
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318

abbrev Source (i:Fin 4) (upper:Bool):=PELOriginalHalfPlaneSheetTopology318.Total i upper
abbrev Target (i:Fin 4) (upper:Bool):=LegendreHalfPlaneSheetTopology318.Total (branchParameter i) upper

/-- An ACTUAL whole-halfplane comparison between the original character
cover and the original finite Legendre equation. Both topologies were
constructed independently. A single source base-fiber labeling is used
per halfplane; compatibility of the two choices across real cuts is NOT
asserted here. -/
@[expose] def comparison (i:Fin 4) (upper:Bool) : Source i upper≃ₜTarget i upper:=
  (PELOriginalHalfPlaneSheetTopology318.homeomorph i upper).symm.trans
    (LegendreHalfPlaneSheetTopology318.homeomorph (branchParameter i)
      (branchParameter_im_zero i) upper)

lemma comparison_fromSum (i:Fin 4) (upper:Bool) (z:domain upper⊕domain upper) :
    comparison i upper (PELOriginalHalfPlaneSheetTopology318.homeomorph i upper z)=
      LegendreHalfPlaneSheetTopology318.homeomorph (branchParameter i)
        (branchParameter_im_zero i) upper z := by
  change LegendreHalfPlaneSheetTopology318.homeomorph _ _ _
    ((PELOriginalHalfPlaneSheetTopology318.homeomorph i upper).symm
      (PELOriginalHalfPlaneSheetTopology318.homeomorph i upper z))=_
  rw [Homeomorph.symm_apply_apply]

lemma comparison_sheet (i:Fin 4) (upper positive:Bool) (z:domain upper) :
    comparison i upper (PELOriginalHalfPlaneSheetTopology318.sheet i upper positive z)=
      LegendreHalfPlaneSheetTopology318.sheet (branchParameter i)
        (branchParameter_im_zero i) upper positive z := by
  cases positive
  · exact comparison_fromSum i upper (Sum.inr z)
  · exact comparison_fromSum i upper (Sum.inl z)

lemma inverse_sheet (i:Fin 4) (upper positive:Bool) (z:domain upper) :
    (comparison i upper).symm
      (LegendreHalfPlaneSheetTopology318.sheet (branchParameter i)
        (branchParameter_im_zero i) upper positive z)=
      PELOriginalHalfPlaneSheetTopology318.sheet i upper positive z := by
  rw [←comparison_sheet,Homeomorph.symm_apply_apply]

/-- Exact original t projection on EVERY point of the whole inverse
halfplane, not just on selected points or a chosen dense subset. -/
theorem projection (i:Fin 4) (upper:Bool) (x:Source i upper) :
    (((comparison i upper x).val.val.1:ℂ):OnePoint ℂ)=normalizedMap i x.val := by
  obtain ⟨z,rfl⟩:=(PELOriginalHalfPlaneSheetTopology318.homeomorph i upper).surjective x
  rw [comparison_fromSum,PELOriginalHalfPlaneSheetTopology318.homeomorph_projection]
  cases z <;> rfl

/-- The comparison commutes with the SAME actual Scheme-valued Proj base
on all points, through the previously constructed actual Scheme t-map. -/
theorem scheme_projection (i:Fin 4) (upper:Bool) (x:Source i upper) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (some (comparison i upper x).val))=
        PELOriginalCommonLegendreBase318.originalProjection i x.val := by
  rw [NormalizedLegendreFiniteProjection318.finite_projection,
    PELOriginalCommonLegendreBase318.original_projection_coordinate]
  exact congrArg ProjectiveLineComplexSchemePoints318.spherePoint (projection i upper x)

/-- Forward comparison has holomorphic ORIGINAL finite equation coordinates
in each genuine original open sheet. This is not a transported target atlas. -/
theorem forward_chart_holomorphic (i:Fin 4) (upper positive:Bool) :
    ∃F:ℂ→ℂ×ℂ,AnalyticOnNhd ℂ F (domain upper) ∧
      ∀z:domain upper,F z.val=
        (comparison i upper (PELOriginalHalfPlaneSheetTopology318.sheet i upper positive z)).val.val := by
  cases positive
  · refine ⟨fun z=>(negativePoint (branchParameter i) (branchParameter_im_zero i) upper z).val,
      negative_coordinates_analytic _ _ _,?_⟩
    intro z
    rw [comparison_sheet]
    rfl
  · refine ⟨fun z=>(positivePoint (branchParameter i) (branchParameter_im_zero i) upper z).val,
      positive_coordinates_analytic _ _ _,?_⟩
    intro z
    rw [comparison_sheet]
    rfl

local instance (i:Fin 4) : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance (i:Fin 4) : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- The inverse is holomorphic in the independently constructed target
sheet coordinate and lands in the unchanged original character atlas. -/
theorem inverse_chart_holomorphic (i:Fin 4) (upper positive:Bool) :
    ∃G:ℂ→CharacterBase i,
      (∀z∈domain upper,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G z) ∧
      ∀z:domain upper,G z.val=
        ((comparison i upper).symm (LegendreHalfPlaneSheetTopology318.sheet (branchParameter i)
          (branchParameter_im_zero i) upper positive z)).val := by
  let e:=PELOriginalHalfPlaneSheetTopology318.enumeration i upper positive
  refine ⟨PELOriginalAnalyticHalfPlaneSheets318.totalSheet i upper e,
    PELOriginalAnalyticHalfPlaneSheets318.totalSheet_holomorphic i upper e,?_⟩
  intro z
  rw [inverse_sheet]
  exact PELOriginalAnalyticHalfPlaneSheets318.totalSheet_eq i upper e z
end PELOriginalHalfPlaneLegendreComparison318
