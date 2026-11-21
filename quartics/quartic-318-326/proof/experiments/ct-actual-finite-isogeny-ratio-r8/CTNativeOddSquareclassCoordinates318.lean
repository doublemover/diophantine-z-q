module
public import CTNativePadicValuationBit318
public import OriginalCasselsOddUnitCharacter318
import all CTNativePadicUnitNormalization318
import all CTNativePadicValuationBit318
import all ActualTwoDescentSquareClassQuotient318
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public section

noncomputable section
namespace CTNativeOddSquareclassCoordinates318

open CTNativePadicValuationBit318 CTNativePadicUnitNormalization318
open ActualTwoDescentSquareClassQuotient318 OriginalCasselsOddUnitCharacter318

variable (p : ℕ) [Fact p.Prime]

def signBit (z : ℤ) : Bit := if z=1 then 0 else 1

private theorem signBit_mul (a b : ℤ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    signBit (a*b)=signBit a+signBit b := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> decide

private theorem signBit_eq_zero (z : ℤ) : signBit z=0 ↔ z=1 := by
  by_cases h : z=1 <;> simp [signBit,h,show (1:Bit)≠0 by decide]

def unitCharBit : (ZMod p)ˣ →* Multiplicative Bit where
  toFun u := Multiplicative.ofAdd (signBit (quadraticChar (ZMod p) (u:ZMod p)))
  map_one' := by
    change signBit (quadraticChar (ZMod p) (↑(1:(ZMod p)ˣ):ZMod p))=0
    rw [Units.val_one, (quadraticChar (ZMod p)).map_one] <;> rfl
  map_mul' u v := by
    change signBit (quadraticChar (ZMod p) (↑(u*v):ZMod p)) =
      signBit (quadraticChar (ZMod p) (u:ZMod p))+signBit (quadraticChar (ZMod p) (v:ZMod p))
    rw [Units.val_mul,map_mul]
    exact signBit_mul _ _
      (quadraticChar_dichotomy u.ne_zero) (quadraticChar_dichotomy v.ne_zero)

def oddUnitCoordinates : ℚ_[p]ˣ →* Multiplicative (Bit × Bit) where
  toFun u := Multiplicative.ofAdd
    ((valuationBit p u).toAdd,(unitCharBit p (residueUnits p u)).toAdd)
  map_one' := by
    change ((valuationBit p 1).toAdd,(unitCharBit p (residueUnits p 1)).toAdd)=(0,0)
    rw [map_one (valuationBit p),map_one (residueUnits p),map_one (unitCharBit p)] <;> rfl
  map_mul' x y := by
    change ((valuationBit p (x*y)).toAdd,(unitCharBit p (residueUnits p (x*y))).toAdd) =
      ((valuationBit p x).toAdd,(unitCharBit p (residueUnits p x)).toAdd) +
      ((valuationBit p y).toAdd,(unitCharBit p (residueUnits p y)).toAdd)
    rw [map_mul (valuationBit p),map_mul (residueUnits p),map_mul (unitCharBit p)] <;> rfl

/-- Actual local squareclass coordinates, factorized through the same
quotient as the actual reciprocal point labels. -/
def oddCoordinates : SquareClass ℚ_[p] →* Multiplicative (Bit × Bit) :=
  liftBitCoordinates p (oddUnitCoordinates p)

theorem normalized_residue_value (u : ℚ_[p]ˣ) :
    (residueUnits p u : ZMod p) = PadicInt.toZMod (normalizedInteger p u) := by
  change PadicInt.toZMod (↑(normalizedUnit p u):ℤ_[p])= _
  exact congrArg PadicInt.toZMod (normalizedIntegralUnit p u).unit_spec

theorem odd_value_coords (x : ℚ_[p]) (hx : x≠0) :
    (oddCoordinates p (classOf x hx)).toAdd =
      ((x.valuation:Bit),
       signBit (quadraticChar (ZMod p) (PadicInt.toZMod (normalizedInteger p (Units.mk0 x hx))))) := by
  rw [oddCoordinates,liftBitCoordinates_on_value]
  change ((x.valuation:Bit), signBit (quadraticChar (ZMod p) (residueUnits p (Units.mk0 x hx):ZMod p))) = _
  rw [normalized_residue_value]

/-- No extra unramified symbol is postulated: zero bits force an actual
square root, by native signed valuation and the odd local unit lift. -/
theorem zero_bits_has_square (hp2 : p≠2) (x : ℚ_[p]) (hx : x≠0)
    (h : oddCoordinates p (classOf x hx)=1) :
    ∃ s : ℚ_[p], s≠0 ∧ x=s^2 := by
  let u := Units.mk0 x hx
  let U := normalizedInteger p u
  have hPair := congrArg Multiplicative.toAdd h
  rw [odd_value_coords] at hPair
  have hV : (x.valuation:Bit)=0 := congrArg Prod.fst hPair
  have hR : signBit (quadraticChar (ZMod p) (PadicInt.toZMod U))=0 := congrArg Prod.snd hPair
  have hU := normalizedIntegralUnit p u
  have hSq : IsSquare (PadicInt.toZMod U) :=
    (quadraticChar_one_iff_isSquare (hU.map PadicInt.toZMod).ne_zero).mp
      ((signBit_eq_zero _).mp hR)
  obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 U hU).mpr hSq
  exact square_of_valuationBit_zero_and_norm_square p x hx hV r hr he

theorem oddCoordinates_injective (hp2 : p≠2) : Function.Injective (oddCoordinates p) :=
  coordinates_injective_of_kernel_square p (oddCoordinates p) (zero_bits_has_square p hp2)

theorem odd_coords_of_integral_unit (U : ℤ_[p]) (hU : IsUnit U) :
    (oddCoordinates p (classOf (U:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hU.ne_zero))).toAdd =
      (0,signBit (quadraticChar (ZMod p) (PadicInt.toZMod U))) := by
  have hV := OriginalCasselsRamifiedResidue318.actual_val_zero_of_unit U hU
  have hN := normalizedInteger_valuative_unit p
    (Units.mk0 (U:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)) U rfl hV
  rw [odd_value_coords,hV,Int.cast_zero,hN]

theorem odd_coords_prime :
    (oddCoordinates p (classOf (p:ℚ_[p]) (padic_prime_ne p))).toAdd=(1,0) := by
  rw [odd_value_coords,Padic.valuation_p,Int.cast_one,normalizedInteger_prime p,
    map_one, (quadraticChar (ZMod p)).map_one] <;> rfl

end CTNativeOddSquareclassCoordinates318

#print axioms CTNativeOddSquareclassCoordinates318.oddCoordinates_injective
