module
public import OriginalTargetHOneCoordinates318

public section
noncomputable section
namespace OriginalFiveHOneNormMatrices318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318 OriginalHOneTraceNormalization318
open ActualSourceHOneCharacterAction318 ActualSourceHOneCharacterProjectors318
open OriginalTargetHOneCoordinates318
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unnormalized trace composed with each actual quotient pullback is8 on its own factor and0 otherwise. -/
theorem trace_pullback_matrix (i j : Index) (y : TargetHOne j) :
    originalTrace i (pullback j y) = if h : i = j then (8 : ℚ) • (h.symm ▸ y) else 0 := by
  rw [original_trace_formula]
  by_cases h : i = j
  · subst j
    rw [dif_pos rfl,split]
  · rw [dif_neg h,OriginalFiveHOneTraceEquivalence318.cross_terms i j h,smul_zero]

/-- Exact degree-eight source identity through all original unnormalized traces. -/
theorem sum_pullback_traces (y : SourceHOne) :
    ∑ i, pullback i (originalTrace i y) = (8 : ℚ) • y := by
  simp only [original_trace_formula]
  have hp (i : Index) : pullback i ((8 : ℚ) • transfer i y) =
      (8 : ℚ) • pullback i (transfer i y) := (pullbackLinear i).map_smul _ _
  simp only [hp,← Finset.smul_sum,OriginalFiveHOneTraceEquivalence318.sum_original_projections]

/-- The actual norm/trace coordinate matrix in the specified target generators is exactly8 times the identity. -/
theorem trace_character_matrix (i j : Index) :
    (OriginalTargetHOneCoordinates318.equivalence i).symm (originalTrace i (characterClass j)) =
      if i = j then 8 else 0 := by
  rw [original_trace_formula,transfer_character]
  by_cases h : i = j
  · simp only [if_pos h]
    change (OriginalTargetHOneCoordinates318.equivalence i).symm
      (OriginalTargetHOneCoordinates318.equivalence i 8) = _
    rw [LinearEquiv.symm_apply_apply]
  · simp only [if_neg h,smul_zero,map_zero]

/-- Original global root signs diagonalize the same actual source map; no separate representation is introduced. -/
theorem sign_trace_character (b : Fin 4 → Bool) (i j : Index) :
    originalTrace i (SchemeSourceCohomology318.pullback (ContactGlobalSigns318.map SourceTwistArithmetic318.units b) 1
      (characterClass j)) =
      SourceHOneCharacterIndices318.epsilon j b • originalTrace i (characterClass j) := by
  rw [ActualSourceHOneGeometricSigns318.geometric_action,action_characterClass]
  exact (originalTrace i).toRatLinearMap.map_smul _ _

end OriginalFiveHOneNormMatrices318
