module
public import ActualTwoDescentNativeFiniteLevels318
public import ActualTwoDescentFieldTorsionSignEquivalence318
public section
noncomputable section
namespace ActualTwoDescentSquareOneBinary318
open ActualTwoDescentFieldSquareOneUnits318
variable {K : Type*} [Field K] [CharZero K]
local instance : DecidableEq (SquareOne K) := Classical.decEq _

lemma actual_negative_one_ne_one : (negativeOne : SquareOne K) ≠ 1 := by
  intro h
  have hval := congrArg (fun u : SquareOne K => ((u : Kˣ) : K)) h
  change (-1 : K)=1 at hval
  have : (2 : K)=0 := by linear_combination -hval
  norm_num at this

lemma actual_negative_one_mul_self : (negativeOne : SquareOne K)*negativeOne=1 := by
  apply Subtype.ext
  change (-1 : Kˣ)*(-1)=1
  simp

/-- Original roots of unity, with 1 mapped to 0 and -1 mapped to 1. -/
def squareOneBit (u : SquareOne K) : ZMod 2 := if u=1 then 0 else 1

@[simp] lemma actual_bit_one : squareOneBit (1 : SquareOne K)=0 := by simp [squareOneBit]
@[simp] lemma actual_bit_negative : squareOneBit (negativeOne : SquareOne K)=1 := by
  simp [squareOneBit,actual_negative_one_ne_one]

lemma actual_bit_mul (u v : SquareOne K) : squareOneBit (u*v)=squareOneBit u+squareOneBit v := by
  rcases actual_square_one_cases u with rfl|rfl <;> rcases actual_square_one_cases v with rfl|rfl
  all_goals norm_num [actual_negative_one_mul_self]

def binarySquareOne (a : ZMod 2) : SquareOne K := if a=0 then 1 else negativeOne

lemma actual_binary_bit_inverse (u : SquareOne K) : binarySquareOne (squareOneBit u)=u := by
  rcases actual_square_one_cases u with rfl|rfl <;> simp [binarySquareOne]

lemma actual_bit_binary_inverse (a : ZMod 2) : squareOneBit (binarySquareOne (K:=K) a)=a := by
  fin_cases a <;> simp [binarySquareOne]

def squareOneBinaryEquiv : SquareOne K ≃* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (squareOneBit u)
  invFun a := binarySquareOne a.toAdd
  left_inv := actual_binary_bit_inverse
  right_inv a := congrArg Multiplicative.ofAdd (actual_bit_binary_inverse a.toAdd)
  map_mul' u v := congrArg Multiplicative.ofAdd (actual_bit_mul u v)

/-- The characteristic-two sign identity, proved on the actual finite ring. -/
lemma actual_binary_neg (a : ZMod 2) : -a=a := by fin_cases a <;> decide

end ActualTwoDescentSquareOneBinary318
