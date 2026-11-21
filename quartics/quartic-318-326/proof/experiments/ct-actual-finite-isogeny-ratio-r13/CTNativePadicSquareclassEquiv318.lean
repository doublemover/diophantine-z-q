module
public import CTNativeOddSquareclassCoordinates318
public import CTNativeDyadicSquareclassCoordinates318
import all CTNativeOddSquareclassCoordinates318
import all CTNativeDyadicSquareclassCoordinates318
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTNativePadicSquareclassEquiv318

open CTNativePadicValuationBit318 CTNativeOddSquareclassCoordinates318
open CTNativeDyadicSquareclassCoordinates318 CTNativePadicUnitNormalization318
open ActualTwoDescentSquareClassQuotient318 OriginalCasselsOddUnitSquare318
open OriginalCasselsDyadicNormalize318 ActualTwoDescentTwoAdicUnits318

private theorem onto_two {G : Type*} [Monoid G] (f : G →* Multiplicative (Bit × Bit))
    (u w : G) (hu : (f u).toAdd=(1,0)) (hw : (f w).toAdd=(0,1)) :
    Function.Surjective f := by
  intro z
  let a := z.toAdd.1
  let b := z.toAdd.2
  refine ⟨u^a.val*w^b.val,Multiplicative.toAdd.injective ?_⟩
  have hb : ∀ a b : Bit,
      a.val • ((1,0):Bit × Bit)+b.val • ((0,1):Bit × Bit)=(a,b) := by decide
  simp only [map_mul,map_pow,Multiplicative.toAdd_mul,Multiplicative.toAdd_pow,hu,hw,hb] <;> rfl

private theorem onto_three {G : Type*} [Monoid G] (f : G →* Multiplicative (Bit × Bit × Bit))
    (u v w : G) (hu : (f u).toAdd=(1,0,0)) (hv : (f v).toAdd=(0,1,0))
    (hw : (f w).toAdd=(0,0,1)) : Function.Surjective f := by
  intro z
  let a := z.toAdd.1
  let b := z.toAdd.2.1
  let c := z.toAdd.2.2
  refine ⟨u^a.val*v^b.val*w^c.val,Multiplicative.toAdd.injective ?_⟩
  have hb : ∀ a b c : Bit,
      a.val • ((1,0,0):Bit × Bit × Bit)+b.val • ((0,1,0):Bit × Bit × Bit)+
        c.val • ((0,0,1):Bit × Bit × Bit)=(a,b,c) := by decide
  simp only [map_mul,map_pow,Multiplicative.toAdd_mul,Multiplicative.toAdd_pow,hu,hv,hw,hb] <;> rfl

section Odd
variable (p : ℕ) [Fact p.Prime]

/-- The second odd coordinate row is an actual mod-p lifted unit,
not a chosen unrelated group generator. -/
theorem actual_odd_nonsquare_unit_coords (hp2 : p≠2) :
    ∃ U : ℤ_[p], ∃ hu : IsUnit U,
      (oddCoordinates p (classOf (U:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hu.ne_zero))).toAdd=(0,1) := by
  have hChar : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨r,hr⟩ := quadraticChar_exists_neg_one' (F:=ZMod p) hChar
  let U : ℤ_[p] := (r:ZMod p).val
  have hRed : PadicInt.toZMod U=(r:ZMod p) := by
    simp only [U,map_natCast,ZMod.natCast_zmod_val]
  have hU : IsUnit U := (residue_nonzero_iff_unit _).mp (fun h => r.ne_zero (hRed.symm.trans h))
  refine ⟨U,hU,?_⟩
  rw [odd_coords_of_integral_unit,hRed,hr] <;> decide

theorem oddCoordinates_surjective (hp2 : p≠2) : Function.Surjective (oddCoordinates p) := by
  obtain ⟨U,hU,hRow⟩ := actual_odd_nonsquare_unit_coords p hp2
  exact onto_two (oddCoordinates p)
    (classOf (p:ℚ_[p]) (padic_prime_ne p))
    (classOf (U:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)) (odd_coords_prime p) hRow

def oddScalarEquiv (hp2 : p≠2) : SquareClass ℚ_[p] ≃* Multiplicative (Bit × Bit) :=
  MulEquiv.ofBijective (oddCoordinates p) ⟨oddCoordinates_injective p hp2,oddCoordinates_surjective p hp2⟩

end Odd

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem dyadic_coords_neg_one :
    (dyadicCoordinates (classOf (-1:ℚ_[2]) (by norm_num))).toAdd=(0,1,0) := by
  have hU : IsUnit (-1:ℤ_[2]) := (isUnit_one : IsUnit (1:ℤ_[2])).neg
  have h := dyadic_coords_of_integral_unit (-1:ℤ_[2]) hU
  have hRes : res8 (-1:ℤ_[2])=(-1:ZMod 8) := by rw [map_neg,map_one]
  have hC : classOf ((-1:ℤ_[2]):ℚ_[2]) (PadicInt.coe_ne_zero.mpr hU.ne_zero) =
      classOf (-1:ℚ_[2]) (by norm_num) :=
    (class_of_eq_iff _ _ _ _).mpr ⟨1,one_ne_zero,by simp only [PadicInt.coe_neg,PadicInt.coe_one,one_pow,mul_one]⟩
  rw [hRes,hC] at h
  simpa only [show epsilonBit (-1:ZMod 8)=1 by decide,show omegaBit (-1:ZMod 8)=0 by decide] using h

theorem dyadicCoordinates_surjective : Function.Surjective dyadicCoordinates :=
  onto_three dyadicCoordinates
    (classOf ((2:ℕ):ℚ_[2]) (padic_prime_ne 2)) (classOf (-1:ℚ_[2]) (by norm_num))
    (classOf (5:ℚ_[2]) (by norm_num))
    dyadic_coords_prime dyadic_coords_neg_one dyadic_coords_five

def dyadicScalarEquiv : SquareClass ℚ_[2] ≃* Multiplicative (Bit × Bit × Bit) :=
  MulEquiv.ofBijective dyadicCoordinates ⟨dyadicCoordinates_injective,dyadicCoordinates_surjective⟩

end CTNativePadicSquareclassEquiv318

#print axioms CTNativePadicSquareclassEquiv318.oddScalarEquiv
#print axioms CTNativePadicSquareclassEquiv318.dyadicScalarEquiv
