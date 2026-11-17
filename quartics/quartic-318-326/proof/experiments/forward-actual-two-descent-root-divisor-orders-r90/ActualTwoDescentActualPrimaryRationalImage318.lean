module
public import ActualTwoDescentRationalPrimaryTransition318
public section
noncomputable section
namespace ActualTwoDescentActualPrimaryRationalImage318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerIntoPrimary318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherRationalImage318

open ActualTwoDescentRationalPrimaryTransition318

/-- Independently defined actual rational primary Kummer image, not designated as a kernel. -/
def rationalPrimaryImage (n : ℚ) (hn : n ≠ 0) : AddSubgroup (actualPrimarySelmer n hn) where
  carrier := {x | ∃ k : ℕ, ∃ P : Point n, rationalPrimaryHom n hn k P=x}
  zero_mem' := ⟨0,0,map_zero _⟩
  add_mem' := by
    rintro x y ⟨i,P,rfl⟩ ⟨j,Q,rfl⟩
    let k := max i j
    refine ⟨k,(2^(k-i)) • P+(2^(k-j)) • Q,?_⟩
    rw [map_add,←actual_rational_primary_transition n hn i k (le_max_left i j),
      ←actual_rational_primary_transition n hn j k (le_max_right i j)]
  neg_mem' := by
    rintro x ⟨k,P,rfl⟩
    exact ⟨k,-P,map_neg _ P⟩

end ActualTwoDescentActualPrimaryRationalImage318
