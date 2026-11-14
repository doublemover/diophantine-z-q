module
public import PELOriginalOrderedCompletedContinuity318
public section
noncomputable section
namespace PELOriginalOrderedCharacterContinuity318
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCharacterQuotient318 PELOriginalOrderedCharacterCoordinate318
open LegendreCompletedPointIdentification318
local instance : TopologicalSpace (FourRootNormalizedPointCharts318.Completed branches):=
  FourRootGluedTopology318.topology branches

@[expose] def comparison (i:Fin 4):CharacterBase i≃LegendrePlaneOverlap318.CompletedPlane (parameter i):=
  (PELOriginalOrderedCharacterPointEquivalence318.equivalence i).trans
    (schemeEquivalence (parameter i)).symm
lemma scheme_square (i:Fin 4) (x:CharacterBase i):
    schemeEquivalence (parameter i) (comparison i x)=
      PELOriginalOrderedCharacterPointMap318.pointMap i x:=
  (schemeEquivalence (parameter i)).apply_symm_apply _

/-- The comparison remains the exact map previously descended from the
whole original source Scheme morphism, now in the independent atlas. -/
lemma source_square (i:Fin 4) (x:UnlevelledBase):comparison i (toCharacter i x)=
    PELOriginalOrderedCompletedChartSquares318.completedMap i
      (PELOriginalCompletedContactBiholomorph318.comparison x):=rfl
lemma source_continuous (i:Fin 4):Continuous (comparison i ∘ toCharacter i):=by
  have he:comparison i ∘ toCharacter i=
      PELOriginalOrderedCompletedChartSquares318.completedMap i ∘
        PELOriginalCompletedContactBiholomorph318.comparison:=funext (source_square i)
  rw [he]
  exact (PELOriginalOrderedCompletedContinuity318.continuous i).comp
    PELOriginalCompletedContactBiholomorph318.comparison.continuous

/-- Continuity descends through the ORIGINAL quotient topology. This does
not transport the independent target topology along the point bijection. -/
theorem continuous (i:Fin 4):Continuous (comparison i):=by
  let descended:CharacterBase i→LegendrePlaneOverlap318.CompletedPlane (parameter i):=
    Quotient.lift (comparison i ∘ toCharacter i) (fun x y h=>by
      exact congrArg (fun q:CharacterBase i=>comparison i q) (Quotient.sound h))
  have hc:Continuous descended:=(source_continuous i).quotient_lift _
  have he:descended=comparison i:=by
    funext x
    refine Quotient.inductionOn x ?_
    intro p
    rfl
  rwa [he] at hc
end PELOriginalOrderedCharacterContinuity318
