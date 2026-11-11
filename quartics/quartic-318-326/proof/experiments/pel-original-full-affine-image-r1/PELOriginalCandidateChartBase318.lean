module
public import PELOriginalCandidateNineChartCover318
public section
noncomputable section
namespace PELOriginalCandidateChartBase318
open AlgebraicGeometry CategoryTheory
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalReducedProjectiveCandidate318 PELOriginalChartSectionField318
open HomogeneousQuotientChartSupport318 PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)

/-- The scalar action used in the actual chart fraction-field and
transcendence calculations is EXACTLY the base action induced by the
original candidate structure map to Spec(C). The affine cover is over
C, not merely an unbased Scheme cover with a separately named algebra. -/
@[reassoc] theorem chart_over_complex_base:
    chartMap τ hτ j≫PELOriginalProperComplexCandidate318.structureMap τ hτ=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j))):=by
  calc
    _=(actualChartIso τ hτ j).hom≫
        ((candidateChart τ hτ j).ι≫inclusion τ hτ)≫
          ComplexProjectiveBase318.structureMap:=by
      simp only [chartMap,PELOriginalProperComplexCandidate318.structureMap,Category.assoc]
    _=(actualChartIso τ hτ j).hom≫
        (toChart τ hτ j≫chartMorphism j)≫ComplexProjectiveBase318.structureMap:=by
      rw [actual_chart_square]
    _=coordinateChartMap τ hτ j≫chartMorphism j≫ComplexProjectiveBase318.structureMap:=by
      simpa only [Category.assoc] using congrArg
        (fun f=>f≫chartMorphism j≫ComplexProjectiveBase318.structureMap)
        (actualChartIso_over τ hτ j)
    _=Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j))):=by
      change Spec.map (CommRingCat.ofHom (HomogeneousQuotientChart318.quotientMap
        (PELOriginalCubicRelationIdeal318.relations τ hτ) j).rangeRestrict)≫
        Proj.awayι _ _ (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num)≫
        (Proj.toSpecZero _≫ComplexProjectiveBase318.baseIso.hom)=_
      simp only [Category.assoc,Proj.awayι_toSpecZero_assoc]
      change Spec.map (CommRingCat.ofHom
        (HomogeneousQuotientChart318.quotientMap
          (PELOriginalCubicRelationIdeal318.relations τ hτ) j).rangeRestrict)≫
        (Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom
            (ComplexProjectiveMarkerPoint318.grading (ι:=Label 3))
            (Submonoid.powers (MvPolynomial.X j))))≫
          Spec.map (CommRingCat.ofHom
            (ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom))=_
      rw [←Spec.map_comp,←Spec.map_comp]
      rfl
end PELOriginalCandidateChartBase318
