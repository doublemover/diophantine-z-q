module
public import CTActualRetainedScalarPair318
public import CTPrimeReciprocityBitCancellation318
import Mathlib.Tactic.NormNum
import all Mathlib.NumberTheory.LegendreSymbol.Basic
public section
noncomputable section

namespace CTActualPrimeScalarRows318

open CTActualRetainedScalarPair318 CTActualFiniteIsogenyLinear318
open CTNativePadicValuationBit318 CTNativePadicUnitNormalization318
open CTNativeOddSquareclassCoordinates318 CTNativeDyadicSquareclassCoordinates318
open CTNativePadicSquareclassEquiv318
open OriginalCasselsOddUnitSquare318 OriginalCasselsDyadicNormalize318
open ActualTwoDescentSquareClassQuotient318

def negOneLabel (K : Type) [Field K] : ScalarBits K :=
  Additive.ofMul (classOf (-1:K) (neg_ne_zero.mpr one_ne_zero))

def primeLabel (K : Type) [Field K] [CharZero K] (q : ℕ) (hq : q≠0) : ScalarBits K :=
  Additive.ofMul (classOf (q:K) (Nat.cast_ne_zero.mpr hq))

theorem actual_real_minus_one : realVector (negOneLabel ℝ)=1 := by
  rw [negOneLabel,realVector_class,if_neg (by norm_num : ¬0<(-1:ℝ))]

theorem actual_real_natural (q : ℕ) (hq : q≠0) : realVector (primeLabel ℝ q hq)=0 := by
  rw [primeLabel,realVector_class,if_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq))]

section Odd
variable (p : ℕ) [Fact p.Prime]

theorem actual_odd_minus_one : oddVector p (negOneLabel ℚ_[p])=(0,oddSign p) := by
  have hU : IsUnit (-1:ℤ_[p]) := (isUnit_one : IsUnit (1:ℤ_[p])).neg
  have hC : classOf ((-1:ℤ_[p]):ℚ_[p]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)=
      classOf (-1:ℚ_[p]) (neg_ne_zero.mpr one_ne_zero) :=
    (class_of_eq_iff _ _ _ _).mpr
      ⟨1,one_ne_zero,by simp only [PadicInt.coe_neg,PadicInt.coe_one,one_pow,mul_one]⟩
  have h := odd_coords_of_integral_unit p (-1:ℤ_[p]) hU
  rw [hC,map_neg,map_one] at h
  rw [negOneLabel,oddVector_class,h]
  congr 1 <;> simp [oddSign,legendreSym]

theorem actual_odd_own :
    oddVector p (primeLabel ℚ_[p] p (Fact.out : p.Prime).ne_zero)=(1,0) := by
  rw [primeLabel,oddVector_class]
  exact odd_coords_prime p

theorem actual_odd_natural_unit (q : ℕ) (hq : q≠0) (hd : ¬p∣q) :
    oddVector p (primeLabel ℚ_[p] q hq)=(0,signBit (legendreSym p q)) := by
  have hU : IsUnit (q:ℤ_[p]) := (residue_nonzero_iff_unit _).mp
    (by rw [map_natCast]; exact fun e => hd ((ZMod.natCast_eq_zero_iff q p).mp e))
  have hC : classOf ((q:ℤ_[p]):ℚ_[p]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)=
      classOf (q:ℚ_[p]) (Nat.cast_ne_zero.mpr hq) :=
    (class_of_eq_iff _ _ _ _).mpr
      ⟨1,one_ne_zero,by simp only [PadicInt.coe_natCast,one_pow,mul_one]⟩
  have h := odd_coords_of_integral_unit p (q:ℤ_[p]) hU
  rw [hC,map_natCast] at h
  rw [primeLabel,oddVector_class,h]
  congr 1 <;> simp [legendreSym]

end Odd

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_dyadic_minus_one : dyadicVector (negOneLabel ℚ_[2])=(0,1,0) := by
  rw [negOneLabel,dyadicVector_class]
  exact dyadic_coords_neg_one

theorem actual_dyadic_two : dyadicVector (primeLabel ℚ_[2] 2 (by decide))=(1,0,0) := by
  rw [primeLabel,dyadicVector_class]
  exact dyadic_coords_prime

theorem actual_dyadic_odd_natural (q : ℕ) (hq : q≠0) (hOdd : q%2=1) :
    dyadicVector (primeLabel ℚ_[2] q hq)=
      (0,epsilonBit (q:ZMod 8),omegaBit (q:ZMod 8)) := by
  have hU : IsUnit (q:ℤ_[2]) := unit_of_mod2_one _ (by
    rw [map_natCast]
    exact (ZMod.natCast_eq_natCast_iff' q 1 2).mpr (by simpa using hOdd))
  have hC : classOf ((q:ℤ_[2]):ℚ_[2]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)=
      classOf (q:ℚ_[2]) (Nat.cast_ne_zero.mpr hq) :=
    (class_of_eq_iff _ _ _ _).mpr
      ⟨1,one_ne_zero,by simp only [PadicInt.coe_natCast,one_pow,mul_one]⟩
  have h := dyadic_coords_of_integral_unit (q:ℤ_[2]) hU
  rw [hC,map_natCast] at h
  rw [primeLabel,dyadicVector_class]
  exact h

end CTActualPrimeScalarRows318

#print axioms CTActualPrimeScalarRows318.actual_odd_natural_unit
#print axioms CTActualPrimeScalarRows318.actual_dyadic_odd_natural
