module
public import ComplexSphereInfinityNormalizationFormula318
public import PELOriginalWholeNativeNegation318
public section
noncomputable section
namespace PELOriginalOrderedBaseSchemeNormalization318
open AlgebraicGeometry CategoryTheory
open PELOriginalOrderedCharacterSchemeMaps318 PELOriginalOrderedCharacterCoordinates318
open ProjectiveLineComplexSchemePoints318
open scoped OnePoint
abbrev P1:=ProjectiveJLine318.scheme ℂ

@[expose] def inverseSlope (i:Fin 4):ℂˣ:=
  Units.mk0 (difference i)⁻¹ (inv_ne_zero (difference_ne_zero i))
@[expose] def offset (i:Fin 4):ℂ:= -branch i 0/difference i
@[expose] def baseNormalization (i:Fin 4):P1≅P1:=
  ProjectiveAffineLine318.iso ℂ (inverseSlope i) (offset i)

lemma ordered_points (i:Fin 4):PELOriginalOrderedCharacterCoordinate318.points i=
    ![∞,(branch i 0:ℂ),(branch i 1:ℂ),(branch i 2:ℂ)]:=by
  rw [PELOriginalOrderedCharacterCoordinate318.literal_points]
  fin_cases i <;> rfl

/-- Actual original analytic base coordinate and actual projective Scheme
automorphism agree at EVERY original maximal-base point. -/
theorem original_coordinate_square (i:Fin 4) (q:PELOriginalMaximalQuotient318.MaximalBase):
    (spherePoint (PELOriginalManuscriptNormalization318.coordinate q)).val≫
      (baseNormalization i).hom=
    (spherePoint (PELOriginalOrderedCharacterCoordinate318.coordinate i q)).val:=by
  unfold PELOriginalOrderedCharacterCoordinate318.coordinate
  simp only [Homeomorph.trans_apply]
  have hi:=PELOriginalOrderedCharacterCoordinate318.points_injective i
  rw [ordered_points] at hi ⊢
  exact ComplexSphereInfinityNormalizationFormula318.actual_scheme_normalization
    (branch i 0) (branch i 1) (branch i 2) hi (difference_ne_zero i) _

lemma over_complex (i:Fin 4):(baseNormalization i).hom≫ProjectiveJLine318.structureMap ℂ=
    ProjectiveJLine318.structureMap ℂ:=
  ProjectiveAffineCharts318.map_over_base ℂ (inverseSlope i) (offset i)

/-- All four literal original marked branches use this same Scheme map;
the order is the old fixed omitted-character order, not a new enumeration. -/
theorem original_marked_square (i j:Fin 4):
    (spherePoint (PELOriginalManuscriptNormalization318.coordinate
      (PELOriginalOrderedCharacterCoordinate318.branches i j).val)).val≫
      (baseNormalization i).hom=
    (spherePoint ((![∞,(0:ℂ),(1:ℂ),
      (PELOriginalOrderedCharacterCoordinate318.parameter i:ℂ)]:Fin 4→OnePoint ℂ) j)).val:=by
  rw [original_coordinate_square]
  exact congrArg (fun z=> (spherePoint z).val)
    (congrFun (PELOriginalOrderedCharacterCoordinate318.branch_values i) j)
end PELOriginalOrderedBaseSchemeNormalization318
