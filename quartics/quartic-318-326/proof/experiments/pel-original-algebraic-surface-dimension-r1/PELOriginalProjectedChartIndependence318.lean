module
public import PELOriginalChartAnalyticEvaluation318
public import PELOriginalLevelThreeLocalImage318
public import OpenComplexPolynomialIndependence318
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public section
noncomputable section
namespace PELOriginalProjectedChartIndependence318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalLevelThreeLocalImage318 PELOriginalAllLevelHolomorphicMap318
open ComplexProjectiveComplexAtlas318
variable (τ:ℂ)(hτ:0<τ.im)
abbrev TargetIndex:={i:Label 3 //i≠(0:Label 3)}
@[expose] def coordinateLabel(j:Label 3)(a:TargetIndex):Label 3:=
  ((omittedEquiv (Label 3) 0 j).symm a).val
@[expose] def coordinateElement(j:Label 3)(a:TargetIndex):CoordinateChart τ hτ j:=
  ratioElement τ hτ j (coordinateLabel j a)
lemma coordinate_evaluation(z:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j z≠0)(a:TargetIndex):
    algebraEvaluation τ hτ z j hj (coordinateElement τ hτ j a)=ratioVector τ hτ 1 j z a:=
  actual_ratio_evaluation τ hτ z j (coordinateLabel j a) hj

/-- Two actual complex-linear combinations of the original chart ratios.
The coefficient matrix is the produced left inverse of the genuine
original map derivative, not a chosen abstract transcendence basis. -/
@[expose] def projectedFunction(x:ComplexVectors)(j:Label 3)(k:Fin 2):CoordinateChart τ hτ j:=
  ∑a:TargetIndex,
    algebraMap ℂ (CoordinateChart τ hτ j) (localProjection τ hτ x j (Pi.single a 1) k)*
      coordinateElement τ hτ j a
lemma projection_expansion(x:ComplexVectors)(j:Label 3)(w:TargetModel 1)(k:Fin 2):
    localProjection τ hτ x j w k=
      ∑a:TargetIndex,localProjection τ hτ x j (Pi.single a 1) k*w a:=by
  have he:w=∑a:TargetIndex,w a • Pi.single a 1:=by
    ext b
    simp [Pi.single_apply]
  conv_lhs=>rw [he]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring
lemma projected_evaluation(x z:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j z≠0)(k:Fin 2):
    algebraEvaluation τ hτ z j hj (projectedFunction τ hτ x j k)=
      localProjection τ hτ x j (ratioVector τ hτ 1 j z) k:=by
  have hs(c:ℂ):algebraEvaluation τ hτ z j hj (algebraMap ℂ (CoordinateChart τ hτ j) c)=c:=
    (algebraEvaluation τ hτ z j hj).commutes c
  simp only [projectedFunction,map_sum,map_mul,hs,coordinate_evaluation]
  exact (projection_expansion τ hτ x j (ratioVector τ hτ 1 j z) k).symm

/-- Actual inverse-function neighborhoods supply evaluations onto an
OPEN subset of C². Hence these two literal chart functions are genuinely
algebraically independent in the SAME candidate coordinate ring. -/
theorem independent(x:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j x≠0):
    AlgebraicIndependent ℂ (projectedFunction τ hτ x j):=by
  obtain ⟨W,hW,hWx,ht,hg,hU,hp,himage⟩:=local_holomorphic_image τ hτ x j hj
  apply OpenComplexPolynomialIndependence318.independent_of_open_evaluations
    (projectedFunction τ hτ x j) W hW ⟨_,hWx⟩
  intro w hw
  let z:ComplexVectors:=(parameterChart τ hτ x j hj).symm w
  have hz:value τ hτ 3 j z≠0:=(hU w hw).2
  refine ⟨algebraEvaluation τ hτ z j hz,?_⟩
  intro k
  rw [projected_evaluation]
  have he:localProjection τ hτ x j (ratioVector τ hτ 1 j z)=w:=hp w hw
  exact congrFun he k

/-- Every original coordinate chart has such an actual point: each
individual entire cubic is nonzero by original Fourier independence. -/
theorem every_chart_independent(j:Label 3):
    ∃x:ComplexVectors,AlgebraicIndependent ℂ (projectedFunction τ hτ x j):=by
  have hx:∃x:ComplexVectors,value τ hτ 3 j x≠0:=by
    by_contra h
    push_neg at h
    exact (original_values_independent τ hτ 3).ne_zero j (funext h)
  obtain ⟨x,hx⟩:=hx
  exact ⟨x,independent τ hτ x j hx⟩
theorem two_le_chart_trdeg(j:Label 3):2≤Algebra.trdeg ℂ (CoordinateChart τ hτ j):=by
  obtain ⟨x,hx⟩:=every_chart_independent τ hτ j
  simpa using hx.cardinalMk_le_trdeg
end PELOriginalProjectedChartIndependence318
