module
public import OriginalCharacterSimplePole318
public import OriginalFivePullbackIndependence318

public section
noncomputable section
namespace OriginalCharacterHOneNonzero318
open SourceTwistArithmetic318 SourceHOneCharacterIndices318
open OriginalCharacterSimplePole318 OriginalCharacterClassPullbacks318
open OriginalSmallPoleResidues318 OriginalInfinityCoefficient318
open ActualSourceHOnePullbacks318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All four complementary-root representatives use exactly the first negative pole. -/
theorem character_position (i : Fin 4) :
    position (smallIndex (some i)) = (0,(smallIndex (some i)).val.1) := by
  revert i
  decide

/-- Evaluate the genuine H1 residue of the literal original quotient pullback. -/
theorem pullback_residue (i : Fin 4) :
    ActualSourceHOneResidueBasis318.residueMap
      (characterPullback i
        (WeierstrassBoundaryClass318.cohomologyClass (publishedA i) (publishedB i)))
      (smallIndex (some i)) =
      InfinityOpenChart318.infinityPoint units (numeratorCoefficient i) := by
  rw [pullback_class,ActualSourceHOneResidueBasis318.residueMap_boundary]
  change OriginalOverlapResidues318.residues units (sourceRepresentative i)
    (position (smallIndex (some i))) = _
  rw [representative_simple_pole,character_position,OriginalSimplePoleResidues318.simple_residue]
  change zeroCoordinate units (smallIndex (some i)).val.1
    (numeratorCoefficient i • ContactHOneOrderBases318.infinityBasis units (smallIndex (some i)).val.1) = _
  rw [zeroCoordinate_smul_basis,if_pos rfl]

/-- Nonzero in actual contact H1, not merely nonzero in its function field. -/
theorem pullback_nonzero (i : Fin 4) :
    characterPullback i
      (WeierstrassBoundaryClass318.cohomologyClass (publishedA i) (publishedB i)) ≠ 0 := by
  intro h
  have he := pullback_residue i
  rw [h,map_zero] at he
  exact numerator_coefficient_nonzero i he.symm

/-- Each specified class is nonzero in the actual target's structure-sheaf H1. -/
theorem target_class_nonzero (i : Fin 4) :
    WeierstrassBoundaryClass318.cohomologyClass (publishedA i) (publishedB i) ≠ 0 := by
  intro h
  apply pullback_nonzero i
  rw [h,map_zero]

/-- The four target nonvanishing inputs are now discharged by the original maps. -/
theorem character_target_nonzero (i : Fin 4) :
    ∃ x : ActualFiveHOneDecomposition318.TargetHOne (some i), x ≠ 0 :=
  ⟨WeierstrassBoundaryClass318.cohomologyClass (publishedA i) (publishedB i),target_class_nonzero i⟩

/-- Only nonvanishing of the fifth target remains for whole-source exhaustion. -/
theorem targets_nonzero_of_fifth
    (h : ∃ x : ActualFiveHOneDecomposition318.TargetHOne none, x ≠ 0) :
    ActualFiveHOneRationalExhaustion318.TargetsNonzero := by
  intro i
  cases i with
  | none => exact h
  | some j => exact character_target_nonzero j

/-- The unchanged sum of all five original quotient pullbacks is bijective
once the still-separate fifth target nonvanishing statement is supplied. -/
theorem original_five_bijective
    (h : ∃ x : ActualFiveHOneDecomposition318.TargetHOne none, x ≠ 0) :
    Function.Bijective ActualFiveHOneRationalExhaustion318.sumLinear :=
  ⟨OriginalFivePullbackIndependence318.sumLinear_injective,
    OriginalFivePullbackIndependence318.sumLinear_surjective (targets_nonzero_of_fifth h)⟩

end OriginalCharacterHOneNonzero318
