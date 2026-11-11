module
public import ActualTwoDescentPrimarySelmerAllDivision318
public section
noncomputable section
namespace ActualTwoDescentRestrictedRationalPrimaryImage318
set_option maxHeartbeats 16000000
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryDivision318
open ActualTwoDescentFullPrimarySelmerTorsion318 ActualTwoDescentPrimaryAllRoots318


open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentFullPrimarySelmerTorsion318


/-- Actual finite-level rational images of a specified subgroup map, independently of any kernel. -/
def restrictedRationalPrimaryImage (n : ℚ) (hn : n ≠ 0) {T : Type} [AddCommGroup T]
    (f : T →+ Point n) : AddSubgroup (actualPrimarySelmer n hn) where
  carrier := {x | ∃ k : ℕ, ∃ t : T, rationalPrimaryHom n hn k (f t)=x}
  zero_mem' := ⟨0,0,by simp⟩
  add_mem' := by
    rintro x y ⟨i,t,rfl⟩ ⟨j,u,rfl⟩
    let k := max i j
    refine ⟨k,(2^(k-i)) • t+(2^(k-j)) • u,?_⟩
    rw [map_add,map_nsmul,map_nsmul,map_add,
      ←actual_rational_primary_transition n hn i k (le_max_left i j),
      ←actual_rational_primary_transition n hn j k (le_max_right i j)]
  neg_mem' := by
    rintro x ⟨k,t,rfl⟩
    exact ⟨k,-t,by simp⟩

end ActualTwoDescentRestrictedRationalPrimaryImage318
