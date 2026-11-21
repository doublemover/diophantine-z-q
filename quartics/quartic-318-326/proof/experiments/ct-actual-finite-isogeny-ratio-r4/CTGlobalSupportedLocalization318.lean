module
public import CTGlobalSupportedSquareclassCode318
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTGlobalSupportedLocalization318

open CTGlobalSupportedSquareclassCode318
open ActualNaturalAllPlacesFinite318 ActualTwoDescentSquareClassQuotient318

theorem real_recovers_sign (n : ℕ) (a b : Code n)
    (h : classOf (scalar n a:ℝ) (Rat.cast_ne_zero.mpr (scalar_ne n a)) =
      classOf (scalar n b:ℝ) (Rat.cast_ne_zero.mpr (scalar_ne n b))) :
    a.1=b.1 := by
  obtain ⟨r,hr,he⟩ := (class_of_eq_iff _ _ _ _).mp h
  have hReal : 0<(scalar n a:ℝ) ↔ 0<(scalar n b:ℝ) := by
    constructor
    · intro hA
      by_contra hB
      have hN : (scalar n a:ℝ)≤0 := by
        rw [he]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hB) (sq_nonneg r)
      exact (not_le_of_gt hA) hN
    · intro hB
      rw [he]
      exact mul_pos hB (sq_pos_of_ne_zero hr)
  have hRat : 0<scalar n a ↔ 0<scalar n b := by
    constructor
    · intro hA
      have hb := hReal.mp (by exact_mod_cast hA)
      exact_mod_cast hb
    · intro hB
      have ha := hReal.mpr (by exact_mod_cast hB)
      exact_mod_cast ha
  have hBit : ∀ x y : ZMod 2, (x=0 ↔ y=0) → x=y := by decide
  exact hBit a.1 b.1 ((scalar_pos_iff n a).symm.trans (hRat.trans (scalar_pos_iff n b)))

/-- At the prime indexed by i, equality of actual localized squareclasses
forces equality of the corresponding rational exponent bit at i. -/
theorem padic_recovers_exponent (n : ℕ) (a b : Code n) (i : Support n) :
    letI : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
    classOf (scalar n a:ℚ_[i.val]) (Rat.cast_ne_zero.mpr (scalar_ne n a)) =
      classOf (scalar n b:ℚ_[i.val]) (Rat.cast_ne_zero.mpr (scalar_ne n b)) → a.2 i=b.2 i := by
  letI : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
  dsimp only
  intro h
  obtain ⟨r,hr,he⟩ := (class_of_eq_iff _ _ _ _).mp h
  have hm := congrArg (fun x : ℚ_[i.val] => (x.valuation : ZMod 2)) he
  rw [Padic.valuation_mul (Rat.cast_ne_zero.mpr (scalar_ne n b)) (pow_ne_zero 2 hr),
      Padic.valuation_pow,Padic.valuation_ratCast,Padic.valuation_ratCast] at hm
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,show (2:ZMod 2)=0 from rfl,
    zero_mul,mul_zero,add_zero,scalar_valuation_bit] using hm

/-- Exact finite diagonal injection into just the actual real and
retained p-adic squareclass groups; no omitted place is needed
to separate the stored global signed support codes. -/
theorem actual_localization_jointly_injective (n : ℕ) (a b : Code n)
    (hReal : classOf (scalar n a:ℝ) (Rat.cast_ne_zero.mpr (scalar_ne n a)) =
      classOf (scalar n b:ℝ) (Rat.cast_ne_zero.mpr (scalar_ne n b)))
    (hPadic : ∀ i : Support n, letI : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
      classOf (scalar n a:ℚ_[i.val]) (Rat.cast_ne_zero.mpr (scalar_ne n a)) =
        classOf (scalar n b:ℚ_[i.val]) (Rat.cast_ne_zero.mpr (scalar_ne n b))) :
    a=b :=
  Prod.ext (real_recovers_sign n a b hReal)
    (funext fun i => padic_recovers_exponent n a b i (hPadic i))

end CTGlobalSupportedLocalization318

#print axioms CTGlobalSupportedLocalization318.actual_localization_jointly_injective
