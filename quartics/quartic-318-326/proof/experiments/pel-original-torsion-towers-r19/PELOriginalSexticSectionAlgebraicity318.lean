module
public import PELOriginalWholeSectionRatioAlgebraic318
public import PELOriginalChartSectionField318
public import PELOriginalProjectedChartIndependence318
public section
noncomputable section
namespace PELOriginalSexticSectionAlgebraicity318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalGradedSectionRing318 PELOriginalSectionMultiplication318
open PELOriginalWholeHZeroDimension318 PELOriginalCubicRelationIdeal318
open PELOriginalChartSectionField318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalLevelThreeLocalImage318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def sectionEmbedding : Ring τ hτ →ₐ[ℂ] SectionField τ hτ :=
  IsScalarTower.toAlgHom ℂ (Ring τ hτ) (SectionField τ hτ)
@[expose] def projectedNumerator (x : ComplexVectors) (j : Label 3) (k : Fin 2) :
    homogeneous τ hτ 3 :=
  ∑ a : TargetIndex,
    localProjection τ hτ x j (Pi.single a 1) k • thetaVector τ hτ 3 (coordinateLabel j a)

lemma cubic_denominator_ne_zero (j : Label 3) :
    sectionEmbedding τ hτ (generators τ hτ j) ≠ 0 := by
  simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j

lemma ratioElement_field (j i : Label 3) :
    algebraEmbedding τ hτ j (ratioElement τ hτ j i) =
      sectionEmbedding τ hτ (generators τ hτ i) /
        sectionEmbedding τ hτ (generators τ hτ j) := by
  change embedding τ hτ j (ratioElement τ hτ j i) = _
  rw [ratioElement,fraction_image]
  simp only [pow_one,variable_image] <;> rfl

/-- The same projected pair, now explicitly inside the full section field. -/
lemma projected_field (x : ComplexVectors) (j : Label 3) (k : Fin 2) :
    algebraEmbedding τ hτ j (projectedFunction τ hτ x j k) =
      sectionEmbedding τ hτ (includeDegree τ hτ 3 (projectedNumerator τ hτ x j k)) /
        sectionEmbedding τ hτ (generators τ hτ j) := by
  simp only [projectedFunction,map_sum,map_mul,AlgHom.commutes,coordinateElement,
    ratioElement_field,projectedNumerator,map_smul,Algebra.smul_def,Finset.sum_div,
    mul_div_assoc] <;> rfl

@[expose] def denominatorSection (j : Label 3) : homogeneous τ hτ 6 :=
  multiply τ hτ 3 3 (thetaVector τ hτ 3 j) (thetaVector τ hτ 3 j)
@[expose] def numeratorSection (x : ComplexVectors) (j : Label 3) (k : Fin 2) :
    homogeneous τ hτ 6 :=
  multiply τ hτ 3 3 (projectedNumerator τ hτ x j k) (thetaVector τ hτ 3 j)

lemma denominator_image (j : Label 3) :
    sectionEmbedding τ hτ (includeDegree τ hτ 6 (denominatorSection τ hτ j)) =
      (sectionEmbedding τ hτ (generators τ hτ j))^2 := by
  rw [denominatorSection,← homogeneous_product,map_mul,pow_two] <;> rfl
lemma denominator_ne_zero (j : Label 3) :
    sectionEmbedding τ hτ (includeDegree τ hτ 6 (denominatorSection τ hτ j)) ≠ 0 := by
  rw [denominator_image]
  exact pow_ne_zero _ (cubic_denominator_ne_zero τ hτ j)

lemma numerator_ratio (x : ComplexVectors) (j : Label 3) (k : Fin 2) :
    sectionEmbedding τ hτ (includeDegree τ hτ 6 (numeratorSection τ hτ x j k)) /
      sectionEmbedding τ hτ (includeDegree τ hτ 6 (denominatorSection τ hτ j)) =
      algebraEmbedding τ hτ j (projectedFunction τ hτ x j k) := by
  rw [numeratorSection,← homogeneous_product,map_mul,denominator_image,projected_field]
  change (sectionEmbedding τ hτ (includeDegree τ hτ 3 (projectedNumerator τ hτ x j k)) *
    sectionEmbedding τ hτ (generators τ hτ j)) / (sectionEmbedding τ hτ (generators τ hτ j))^2 = _
  field_simp [cubic_denominator_ne_zero τ hτ j] <;> ring

@[expose] def projectedSectionBase (x : ComplexVectors) (j : Label 3) :
    Subalgebra ℂ (SectionField τ hτ) :=
  Algebra.adjoin ℂ (Set.range
    (fun k => algebraEmbedding τ hτ j (projectedFunction τ hτ x j k)))

/-- EVERY actual full sextic section divided by the SAME cubic chart
section squared is algebraic over the SAME independent projected pair.
This is algebraicity in the full original section field, not an assertion
of membership in the candidate fraction field or regularity on the chart. -/
theorem whole_sextic_ratio_algebraic (x : ComplexVectors) (j : Label 3)
    (hx : value τ hτ 3 j x ≠ 0) (s : homogeneous τ hτ 6) :
    IsAlgebraic (projectedSectionBase τ hτ x j)
      (sectionEmbedding τ hτ (includeDegree τ hτ 6 s) /
        (sectionEmbedding τ hτ (generators τ hτ j))^2) := by
  have hi : AlgebraicIndependent ℂ
      (fun k => algebraEmbedding τ hτ j (projectedFunction τ hτ x j k)) :=
    (independent τ hτ x j hx).map' (f := algebraEmbedding τ hτ j) (embedding_injective τ hτ j)
  have hi' : AlgebraicIndependent ℂ
      (fun k => sectionEmbedding τ hτ (includeDegree τ hτ 6 (numeratorSection τ hτ x j k)) /
        sectionEmbedding τ hτ (includeDegree τ hτ 6 (denominatorSection τ hτ j))) := by
    simpa only [numerator_ratio] using hi
  have h := PELOriginalWholeSectionRatioAlgebraic318.isAlgebraic τ hτ
    (sectionEmbedding τ hτ) 6 (by decide) (denominatorSection τ hτ j)
    (numeratorSection τ hτ x j) (denominator_ne_zero τ hτ j) hi' s
  simpa only [numerator_ratio,denominator_image,projectedSectionBase] using h

/-- In particular, all36 genuine original level-six theta coordinates have
this algebraicity, without requiring quadratic multiplication surjectivity. -/
theorem theta_six_ratio_algebraic (x : ComplexVectors) (j : Label 3)
    (hx : value τ hτ 3 j x ≠ 0) (r : Label 6) :
    IsAlgebraic (projectedSectionBase τ hτ x j)
      (sectionEmbedding τ hτ (includeDegree τ hτ 6 (thetaVector τ hτ 6 r)) /
        (sectionEmbedding τ hτ (generators τ hτ j))^2) :=
  whole_sextic_ratio_algebraic τ hτ x j hx (thetaVector τ hτ 6 r)
end PELOriginalSexticSectionAlgebraicity318
