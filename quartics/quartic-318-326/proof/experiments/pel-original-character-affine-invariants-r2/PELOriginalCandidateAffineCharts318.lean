module
public import HomogeneousQuotientChartSupport318
public import ReducedClosedChartComparison318
public import PELOriginalProperComplexCandidate318
public import PELOriginalRelationKernelIntersection318
public section
noncomputable section
namespace PELOriginalCandidateAffineCharts318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalCubicRelationIdeal318
open PELOriginalLevelTheta318 HomogeneousQuotientChart318 HomogeneousQuotientChartSupport318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
local instance standardGrading:GradedAlgebra degrees:=MvPolynomial.gradedAlgebra
@[expose] def ambientChart:ambient.Opens:=Proj.basicOpen degrees (MvPolynomial.X j)
@[expose] def candidateChart:(candidate τ hτ).Opens:=(inclusion τ hτ) ⁻¹ᵁ ambientChart j
@[expose] def ambientChartIso:(ambientChart j).toScheme≅Spec (CommRingCat.of (Chart j)):=
  Proj.basicOpenIsoSpec degrees (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num)
@[expose] def toChart:(candidateChart τ hτ j).toScheme⟶Spec (CommRingCat.of (Chart j)):=
  ((inclusion τ hτ) ∣_ ambientChart j)≫(ambientChartIso j).hom
instance toChart_closed:IsClosedImmersion (toChart τ hτ j):=by
  dsimp [toChart]
  infer_instance
instance chart_reduced:IsReduced (candidateChart τ hτ j).toScheme:=by
  haveI:IsReduced (candidate τ hτ):=reduced τ hτ
  infer_instance
@[reassoc] lemma actual_chart_square:
    toChart τ hτ j≫chartMorphism j=(candidateChart τ hτ j).ι≫inclusion τ hτ:=by
  simp only [toChart,chartMorphism,Proj.awayι,ambientChartIso,ambientChart,
    Category.assoc,Iso.hom_inv_id_assoc,Scheme.Hom.morphismRestrict_ι]
lemma actual_chart_range:
    Set.range (toChart τ hτ j)=(chartMorphism j) ⁻¹' (zeroSet τ hτ:Set ambient):=by
  ext q
  rw [←inclusion_range]
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨x.val,?_⟩
    exact (congrArg (fun f=>f x) (actual_chart_square τ hτ j)).symm
  · rintro ⟨x,hx⟩
    have hxU:x∈candidateChart τ hτ j:=by
      change inclusion τ hτ x∈ambientChart j
      rw [hx]
      exact chart_nonvanishing j q
    refine ⟨⟨x,hxU⟩,?_⟩
    apply (chartMorphism j).isOpenEmbedding.injective
    exact (congrArg (fun f=>f ⟨x,hxU⟩) (actual_chart_square τ hτ j)).trans hx

abbrev CoordinateChart:=degreeZero (relations τ hτ) j
@[expose] def coordinateChartMap:Spec (CommRingCat.of (CoordinateChart τ hτ j))⟶
    Spec (CommRingCat.of (Chart j)):=
  Spec.map (CommRingCat.ofHom (quotientMap (relations τ hτ) j).rangeRestrict)
instance coordinateChart_closed:IsClosedImmersion (coordinateChartMap τ hτ j):=
  IsClosedImmersion.spec_of_surjective _ (RingHom.rangeRestrict_surjective _)
instance coordinateChart_reduced:IsReduced (Spec (CommRingCat.of (CoordinateChart τ hτ j))):=by
  haveI:(relations τ hτ).IsRadical:=PELOriginalRelationKernelIntersection318.relations_radical τ hτ
  haveI:IsReduced (QuotientRing (relations τ hτ)):=inferInstance
  haveI:IsReduced (LocalizedQuotient (relations τ hτ) j):=inferInstance
  infer_instance
lemma coordinateChart_range:
    Set.range (coordinateChartMap τ hτ j)=(chartMorphism j) ⁻¹' (zeroSet τ hτ:Set ambient):=by
  have hk:RingHom.ker (quotientMap (relations τ hτ) j).rangeRestrict=
      RingHom.ker (quotientMap (relations τ hτ) j):=by
    ext a
    exact Subtype.ext_iff
  rw [coordinateChartMap,PrimeSpectrum.range_comap_of_surjective _ _
    (RingHom.rangeRestrict_surjective _),hk]
  ext q
  change RingHom.ker (quotientMap (relations τ hτ) j)≤q.asIdeal↔
    (relations τ hτ:Set Equations)⊆(chartMorphism j q).asHomogeneousIdeal
  exact kernel_support j (relations τ hτ) (relations_homogeneous τ hτ) q

/-- Actual coordinate ring of the SAME candidate affine chart, identified
with the full degree-zero localization of its LITERAL produced relation
quotient. The isomorphism commutes with the original ambient chart map.
This compares all scheme points and sheaves, not just complex points. -/
@[expose] def actualChartIso:Spec (CommRingCat.of (CoordinateChart τ hτ j))≅
    (candidateChart τ hτ j).toScheme:=
  ReducedClosedChartComparison318.comparison (coordinateChartMap τ hτ j) (toChart τ hτ j)
    ((coordinateChart_range τ hτ j).trans (actual_chart_range τ hτ j).symm)
@[reassoc] lemma actualChartIso_over:
    (actualChartIso τ hτ j).hom≫toChart τ hτ j=coordinateChartMap τ hτ j:=
  ReducedClosedChartComparison318.comparison_over _ _ _
end PELOriginalCandidateAffineCharts318
