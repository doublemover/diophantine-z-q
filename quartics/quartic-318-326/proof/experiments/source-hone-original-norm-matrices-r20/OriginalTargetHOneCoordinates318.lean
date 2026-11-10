module
public import OriginalHOneTraceNormalization318

public section
noncomputable section
namespace OriginalTargetHOneCoordinates318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318 ActualSourceHOneCharacterAction318
open ActualSourceHOneCharacterProjectors318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Canonical target generator obtained from the original source residue class by its original trace/8. -/
@[expose] def generator (i : Index) : TargetHOne i := transfer i (characterClass i)

theorem pullback_generator (i : Index) : pullback i (generator i) = characterClass i := by
  change pullback i (transfer i (characterClass i)) = _
  rw [OriginalFiveHOneTraceEquivalence318.projection_eq_character,projector_characterClass,if_pos rfl]

theorem generator_nonzero (i : Index) : generator i ≠ 0 := by
  intro h
  have hp := pullback_generator i
  rw [h,map_zero] at hp
  exact ActualSourceHOneResidueBasis318.character_coordinates_nonzero i hp.symm

@[expose] def line (i : Index) : ℚ →ₗ[ℚ] TargetHOne i where
  toFun q := q • generator i
  map_add' q r := add_smul q r _
  map_smul' q r := mul_smul q r _

theorem line_injective (i : Index) : Function.Injective (line i) := by
  intro q r h
  have hz : (q-r) • generator i = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (generator_nonzero i))

theorem line_surjective (i : Index) : Function.Surjective (line i) := by
  intro y
  obtain ⟨q,hq⟩ := OriginalFivePullbackIndependence318.pullback_line i y
  refine ⟨q,?_⟩
  apply Function.LeftInverse.injective (split i)
  change pullbackLinear i (q • generator i) = pullback i y
  rw [map_smul,show pullbackLinear i (generator i) = characterClass i from pullback_generator i,hq]

/-- A coordinate on the original target H1 with specified, original-map-compatible generator. -/
@[expose] def equivalence (i : Index) : ℚ ≃ₗ[ℚ] TargetHOne i :=
  LinearEquiv.ofBijective (line i) ⟨line_injective i,line_surjective i⟩

theorem equivalence_apply (i : Index) (q : ℚ) : equivalence i q = q • generator i := rfl

theorem target_finrank_one (i : Index) : Module.finrank ℚ (TargetHOne i) = 1 := by
  have h := (equivalence i).finrank_eq
  simpa using h.symm

/-- Original pullback in these coordinates is exactly the named original source character class. -/
theorem pullback_coordinates (i : Index) (q : ℚ) :
    pullback i (equivalence i q) = q • characterClass i := by
  change pullbackLinear i (q • generator i) = _
  rw [map_smul,show pullbackLinear i (generator i) = characterClass i from pullback_generator i]

/-- Every original normalized transfer has the exact Kronecker matrix on source character coordinates. -/
theorem transfer_character (i j : Index) :
    transfer i (characterClass j) = if i = j then generator i else 0 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    rfl
  · rw [if_neg h]
    exact OriginalFiveHOneTraceEquivalence318.transfer_character_zero i j h

end OriginalTargetHOneCoordinates318
