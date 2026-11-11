module
public import PELOriginalCharacterAlgebraicRelabeling318
public import ComplexLegendreCoordinates318
public section
noncomputable section
namespace PELOriginalOrderedLegendreInvariants318
open PELOriginalManuscriptNormalization318
open PELOriginalOrderedCharacterCoordinate318
open NormalizedLegendreProjectiveModel318

/-- The invariant of the ACTUAL correctly ordered candidate Legendre
curve, not an invariant attached to an arbitrary reordered branch list. -/
@[expose] def invariant (i:Fin 4) : ℂ:=by
  letI := curve_elliptic (parameter i) (parameter_nonexceptional i).1
    (parameter_nonexceptional i).2
  exact (curve (parameter i)).j

lemma invariant_formula (i:Fin 4) :
    invariant i=ComplexLegendreCoordinates318.legendreJ (parameter i) := by
  have h:=curve_j (parameter i) (parameter_nonexceptional i).1
    (parameter_nonexceptional i).2
  change invariant i=256*((parameter i)^2-parameter i+1)^3/
    ((parameter i)^2*(parameter i-1)^2) at h
  rw [h]
  unfold ComplexLegendreCoordinates318.legendreJ
  congr 1
  · congr 1
    ring
  · ring

/-- Exact row map from coordinate characters to the original published
quartic rows. The existing character order105,70,42,30 is reversed. -/
theorem invariant_vector : (fun i:Fin 4=>invariant i)=
    ![ComplexLegendreCoordinates318.legendreJ ((mu-1)/(lambda-1)),
      ComplexLegendreCoordinates318.legendreJ (mu/lambda),
      ComplexLegendreCoordinates318.legendreJ mu,
      ComplexLegendreCoordinates318.legendreJ lambda] := by
  funext i
  rw [invariant_formula,parameter_formula]
  fin_cases i <;> rfl

/-- Final arithmetic convention consumer. The FOUR actual invariant
identifications remain explicit geometric inputs: neither common branch
cardinality nor rational numerical checks supply them. Once provided for
the correctly labeled candidate curves, the existing exact solver derives
the rational original coordinates, rather than assuming them. -/
theorem manuscript_parameters_of_published_invariants
    (h30 : invariant 3=(ContactCoordinates318.quarticJ (-43) (-686) (-2915) (-1372) (-172):ℂ))
    (h42 : invariant 2=(ContactCoordinates318.quarticJ (-43) 600 (-986) (-600) (-43):ℂ))
    (h70 : invariant 1=(ContactCoordinates318.quarticJ (-43) 256 (-130) (-768) (-387):ℂ))
    (h105 : invariant 0=(ContactCoordinates318.quarticJ (-43) 2 505 12 (-1548):ℂ)) :
    lambda=2401 ∧ mu= -343/32 := by
  have h3:=congrFun invariant_vector 3
  have h2:=congrFun invariant_vector 2
  have h1:=congrFun invariant_vector 1
  have h0:=congrFun invariant_vector 0
  exact ComplexLegendreCoordinates318.coordinates_of_original_models lambda mu
    lambda_ne_zero lambda_ne_one mu_ne_zero mu_ne_one
    (h3.symm.trans h30) (h2.symm.trans h42) (h1.symm.trans h70) (h0.symm.trans h105)
end PELOriginalOrderedLegendreInvariants318
