module
public import OriginalInertiaFieldReconstruction318
public import Mathlib.Algebra.BigOperators.Associated
public section
noncomputable section
open scoped BigOperators
namespace LabeledContactInertiaSigns318
open Polynomial SourceTwistArithmetic318 LinearContactSquareclass318
open FourBinaryCharacters318 OriginalInertiaFieldReconstruction318

lemma group_square (w : FourBinaryCharacters318.Group) : w * w = 1 := by
  funext i
  have hh : ∀ x : ZMod 2, x + x = 0 := by decide
  change Multiplicative.ofAdd (Multiplicative.toAdd (w i) + Multiplicative.toAdd (w i)) =
    Multiplicative.ofAdd (0 : ZMod 2)
  exact congrArg Multiplicative.ofAdd (hh (Multiplicative.toAdd (w i)))

lemma flip_ne_one (k : Fin 4) : FourBinaryCharacters318.flip k ≠ 1 := by
  intro h
  have hh := congrArg (fun w : FourBinaryCharacters318.Group => Multiplicative.toAdd (w k)) h
  norm_num [FourBinaryCharacters318.flip] at hh

lemma complementary_at_flip {F : Type*} [Field F] (i k : Fin 4) :
    complementary (F := F) i (FourBinaryCharacters318.flip k) = if i = k then 1 else -1 := by
  fin_cases i <;> fin_cases k <;>
    norm_num [complementary, coordinate, FourBinaryCharacters318.flip, complement, Fin.prod_univ_succ]

lemma linear_dvd_cubic (i k : Fin 4) :
    (X - C (contacts k) : ℚ[X]) ∣ cubic i ↔ i ≠ k := by
  rw [Polynomial.dvd_iff_isRoot]
  fin_cases i <;> fin_cases k <;>
    norm_num [Polynomial.IsRoot, cubic, complement, contacts, Fin.prod_univ_succ]

lemma prime_dvd_cubic (q : ℚ[X]) (k : Fin 4)
    (hcontact : Associated q (X - C (contacts k))) (i : Fin 4) :
    q ∣ cubic i ↔ i ≠ k :=
  hcontact.dvd_iff_dvd_left.trans (linear_dvd_cubic i k)

/-- A prime outside the original four finite contacts divides none of the
original complementary cubics. Nonrational closed points are included. -/
lemma outside_cubics (q : ℚ[X]) (hq : Prime q)
    (hout : ∀ k, ¬ Associated q (X - C (contacts k))) (i : Fin 4) :
    ¬ q ∣ cubic i := by
  intro hd
  obtain ⟨j, _, hj⟩ := (hq.dvd_finsetProd_iff
    (fun j : Fin 3 => (X - C (contacts (complement i j)) : ℚ[X]))).mp hd
  exact hout (complement i j)
    (hq.irreducible.associated_of_dvd (irreducible_X_sub_C _) hj)

variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L]

lemma original_involution
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (σ : L ≃ₐ[RatFunc ℚ] L) (x : L) : σ (σ x) = x := by
  have hh : σ * σ = 1 := by
    apply labels.injective
    rw [map_mul, map_one]
    exact group_square (labels σ)
  exact congrArg (fun e : L ≃ₐ[RatFunc ℚ] L => e x) hh

lemma original_sign
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (σ : L ≃ₐ[RatFunc ℚ] L) (k : Fin 4) (hlabel : labels σ = FourBinaryCharacters318.flip k)
    (q : ℚ[X]) (hcontact : Associated q (X - C (contacts k))) (i : Fin 4) :
    GaloisCharacterContactReconstruction318.character labels i σ =
      if expectedBit q i then -1 else 1 := by
  change complementary (F := RatFunc ℚ) i (labels σ) = _
  rw [hlabel, complementary_at_flip]
  have hd := prime_dvd_cubic q k hcontact i
  by_cases h : i = k
  · have hn : ¬ q ∣ cubic i := fun hdiv => (hd.mp hdiv) h
    rw [if_pos h,(expectedBit_false q i).mpr hn]
    rfl
  · have hp : q ∣ cubic i := hd.mpr h
    simp [expectedBit, h, hp]
end LabeledContactInertiaSigns318
