module
public import ActualTwoDescentHigherSelmerStep318
public section
noncomputable section
namespace ActualTwoDescentHigherShaStep318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

open ActualTwoDescentActualShaPower318 ActualTwoDescentHigherSelmerToSha318 ActualTwoDescentHigherSelmerStep318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherCohomologyStep318

def higherShaStep (n : ℚ) (hn : n ≠ 0) (k : ℕ) : actualShaPower n hn k →+ actualShaPower n hn (k+1) where
  toFun x := ⟨x.val,x.property.1,by rw [pow_succ,Nat.mul_comm,mul_smul,x.property.2,nsmul_zero]⟩
  map_zero' := rfl
  map_add' x y := rfl

lemma actual_higher_selmer_sha_step (n : ℚ) (hn : n ≠ 0) (k : ℕ) (x : actualHigherSelmer n hn k) :
    higherSelmerToSha n hn (k+1) (higherSelmerStep n hn k x)=higherShaStep n hn k (higherSelmerToSha n hn k x) := by
  apply Subtype.ext
  exact actual_higher_step_full_class n hn k x.val

end ActualTwoDescentHigherShaStep318
