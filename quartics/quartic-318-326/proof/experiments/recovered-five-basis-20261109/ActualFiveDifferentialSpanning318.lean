module
public import SingleFlipInvariantLine318
public import ActualDifferentialSignLinear318
public import ActualFifthInvariantLine318
public import Mathlib.Tactic.Module

public section
noncomputable section
namespace ActualFiveDifferentialSpanning318
open AlgebraicGeometry SourceTwistArithmetic318
open ActualFiveRationalIndependent318 ActualDifferentialSignLinear318
open scoped BigOperators
attribute [local instance] rationalModule
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def projection (i : Fin 4) (s : G) : G :=
  (1 / 2 : ℚ) • (s + action (SourceCharacterFields318.flip i) s)

theorem projection_fixed (i : Fin 4) (s : G) :
    action (SourceCharacterFields318.flip i) (projection i s) = projection i s := by
  simp only [projection, map_smul, map_add, involution]
  rw [add_comm]

theorem projection_line (i : Fin 4) (s : G) :
    ∃ a : ℚ, projection i s = a • ContactCharacterDifferentials318.differential i :=
  SingleFlipInvariantLine318.exists_rational_multiple i _ (projection_fixed i s)

theorem projection_sum (i : Fin 4) (s : G) :
    s + action (SourceCharacterFields318.flip i) s = (2 : ℚ) • projection i s := by
  rw [projection, smul_smul]
  norm_num

theorem sum_flip (i : Fin 4) (a : Fin 4 → ℚ) :
    action (SourceCharacterFields318.flip i)
        (∑ j, a j • ContactCharacterDifferentials318.differential j) +
        (∑ j, a j • ContactCharacterDifferentials318.differential j) =
      (2 : ℚ) • (a i • ContactCharacterDifferentials318.differential i) := by
  classical
  rw [map_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j : Fin 4, if i = j then
          (2 : ℚ) • (a i • ContactCharacterDifferentials318.differential i) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, flip_character]
      by_cases h : i = j
      · subst j
        simp [two_smul]
      · simp [h]
    _ = _ := by simp

/-- Every actual global regular differential is a rational linear combination
of the same five actual elliptic pullbacks. The proof uses the four
single-involution fixed lines and the original fifth descent. -/
theorem exists_coefficients (s : G) :
    ∃ a : Fin 4 → ℚ, ∃ b : ℚ,
      s = (∑ i, a i • ContactCharacterDifferentials318.differential i) +
        b • FifthActualDifferential318.differential := by
  choose a ha using fun i => projection_line i s
  let t : G := ∑ i, a i • ContactCharacterDifferentials318.differential i
  let r : G := s - t
  have hr (i : Fin 4) : action (SourceCharacterFields318.flip i) r = -r := by
    have hst : s + action (SourceCharacterFields318.flip i) s =
        t + action (SourceCharacterFields318.flip i) t := by
      rw [projection_sum, ha]
      exact (sum_flip i a).symm.trans (add_comm _ _)
    apply eq_neg_of_add_eq_zero_left
    dsimp only [r]
    rw [map_sub]
    calc
      action (SourceCharacterFields318.flip i) s - action (SourceCharacterFields318.flip i) t +
          (s - t) = (s + action (SourceCharacterFields318.flip i) s) -
            (t + action (SourceCharacterFields318.flip i) t) := by abel
      _ = 0 := sub_eq_zero.mpr hst
  have hf : FifthDifferentialInvariantSummand318.Fixed r := by
    intro b hb
    have he : FifthOpenSigns318.epsilon b = 1 := (Finset.mem_filter.mp hb).2
    change action b r = r
    rw [full_character_of_flips r hr, he, one_smul]
  obtain ⟨b, hb, _⟩ := (ActualFifthInvariantLine318.fixed_iff_existsUnique r).mp hf
  refine ⟨a, b, ?_⟩
  change b • FifthActualDifferential318.differential = s - t at hb
  change s = t + b • FifthActualDifferential318.differential
  rw [hb]
  abel

end ActualFiveDifferentialSpanning318
