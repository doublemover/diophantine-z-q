module
public import SourceTwistArithmetic318
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
open scoped BigOperators
namespace FourBinaryCharacters318
abbrev Group := Fin 4 → Multiplicative (ZMod 2)
variable {F : Type*} [Field F]

/-- The literal sign character in the four specified inertia-basis coordinates. -/
@[expose] def coordinate (i : Fin 4) : Group →* F where
  toFun w := if Multiplicative.toAdd (w i) = 0 then 1 else -1
  map_one' := by simp
  map_mul' w v := by
    change (if Multiplicative.toAdd (w i) + Multiplicative.toAdd (v i) = 0 then 1 else -1) =
      (if Multiplicative.toAdd (w i) = 0 then 1 else -1) *
      (if Multiplicative.toAdd (v i) = 0 then 1 else -1)
    have cases_two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rcases cases_two (Multiplicative.toAdd (w i)) with h | h <;>
      rcases cases_two (Multiplicative.toAdd (v i)) with k | k <;>
      simp [h, k, htwo]

lemma coordinate_square (i : Fin 4) (w : Group) : (coordinate (F := F) i w) ^ 2 = 1 := by
  change (if Multiplicative.toAdd (w i) = 0 then (1 : F) else -1) ^ 2 = 1
  split <;> simp

/-- Omit one finite contact, exactly as in the old three-root character maps. -/
@[expose] def complementary (i : Fin 4) : Group →* F where
  toFun w := ∏ j : Fin 3, coordinate (SourceTwistArithmetic318.complement i j) w
  map_one' := by simp
  map_mul' w v := by simp only [map_mul, Finset.prod_mul_distrib]

lemma complementary_square (i : Fin 4) (w : Group) : (complementary (F := F) i w) ^ 2 = 1 := by
  simp only [complementary, MonoidHom.coe_mk, OneHom.coe_mk, ← Finset.prod_pow,
    coordinate_square, Finset.prod_const_one]

@[expose] def flip (i : Fin 4) : Group :=
  fun j => Multiplicative.ofAdd (if j = i then 1 else 0)

lemma complementary_flip (i : Fin 4) :
    complementary (F := F) i (flip (SourceTwistArithmetic318.complement i 0)) = -1 := by
  fin_cases i <;>
    norm_num [complementary, coordinate, flip, SourceTwistArithmetic318.complement,
      Fin.prod_univ_succ]

variable [CharZero F]
theorem complementary_nontrivial (i : Fin 4) :
    ∃ w : Group, complementary (F := F) i w ≠ 1 := by
  refine ⟨flip (SourceTwistArithmetic318.complement i 0), ?_⟩
  rw [complementary_flip]
  norm_num

@[expose] def signPattern (w : Group) : Fin 4 → Bool :=
  fun i => if Multiplicative.toAdd (w i) = 0 then false else true

lemma card : Nat.card Group = 16 := by
  simp [Group, Nat.card_eq_fintype_card]
end FourBinaryCharacters318
