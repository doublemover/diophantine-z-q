module
public import OriginalFiveHOneTraceEquivalence318

public section
noncomputable section
namespace OriginalHOneTraceNormalization318
open AlgebraicGeometry CategoryTheory
open StructureAdditiveSheaf318 ActualQuotientSheafRetraction318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalization is exactly postcomposition with the original structural scalar sheaf map. -/
theorem retraction_eq {X Y : Scheme.{0}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of ℚ)) (t : pushed f ⟶ sheaf Y) :
    NormalizedStructureTrace318.retraction f p t = t ≫ StructureRationalScalar318.multiply p (1/8) := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rfl

/-- The original source-H1 comparison inverse does not change the normalization factor. -/
theorem normalized_transfer {X Y : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Y) [IsAffineHom f] (p : Y ⟶ Spec (CommRingCat.of ℚ))
    (t : pushed f ⟶ sheaf Y) (y : SheafCohomologyRetraction318.structureH X 1) :
    letI := CohomologyRationalScalar318.structureModule p 1
    AffineHOneComparison318.transfer f (NormalizedStructureTrace318.retraction f p t) y =
      (1/8 : ℚ) • AffineHOneComparison318.transfer f t y := by
  letI := CohomologyRationalScalar318.structureModule p 1
  change Sheaf.H.map (NormalizedStructureTrace318.retraction f p t) 1
    ((AffineHOneComparison318.equivalence f).symm y) = _
  rw [retraction_eq,Sheaf.H.map_comp_apply]
  all_goals rfl

local instance sourceIntegral : IsIntegral (ContactGlobalSmooth318.Model SourceTwistArithmetic318.units) :=
  ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
local instance characterFinite (i : Fin 4) : IsFinite (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterFinite318.completedMap_finite i
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite

/-- Unnormalized original trace on actual common-source H1, not a renamed scalar multiple. -/
@[expose] def originalTrace : (i : Index) → SourceHOne →+ TargetHOne i
  | none => AffineHOneComparison318.transfer FifthCompletedGlobal318.map fifthTrace
  | some i => AffineHOneComparison318.transfer (CompletedCharacterGlobal318.completedMap i) (characterTrace i)

theorem normalized_formula (i : Index) (y : SourceHOne) :
    transfer i y = (1/8 : ℚ) • originalTrace i y := by
  cases i with
  | none => exact normalized_transfer FifthCompletedGlobal318.map ActualHOneRational318.fifthMap fifthTrace y
  | some j => exact normalized_transfer (CompletedCharacterGlobal318.completedMap j)
      (ActualHOneRational318.characterMap j) (characterTrace j) y

theorem original_trace_formula (i : Index) (y : SourceHOne) : originalTrace i y = (8 : ℚ) • transfer i y := by
  rw [normalized_formula,smul_smul]
  norm_num

end OriginalHOneTraceNormalization318
