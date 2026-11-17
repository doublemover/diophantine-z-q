module
public import ActualTwoDescentActualHigherSelmerGrowth318
public section
noncomputable section
namespace ActualTwoDescentHigherTorsionStep318
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

open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentPowerValuedCocycles318

def higherTorsionStep (n : F) (k : ℕ) : geometricPowerTorsion n k →+ geometricPowerTorsion n (k+1) where
  toFun T := ⟨T.val,by
    change (2^(k+1)) • T.val=0
    rw [pow_succ,Nat.mul_comm,mul_smul]
    have h : (2^k) • T.val=0 := T.property
    rw [h,nsmul_zero]⟩
  map_zero' := rfl
  map_add' T U := rfl

def higherCocycleStep (n : F) (hn : n ≠ 0) (k : ℕ) : powerValuedCocycles n hn k →+ powerValuedCocycles n hn (k+1) where
  toFun z := ⟨z.val,by intro σ; rw [pow_succ,Nat.mul_comm,mul_smul,z.property σ,nsmul_zero]⟩
  map_zero' := rfl
  map_add' z w := rfl

end ActualTwoDescentHigherTorsionStep318
