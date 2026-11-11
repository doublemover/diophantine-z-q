module
public import ActualTwoDescentPrimaryClassEventualEquality318
public section
noncomputable section
namespace ActualTwoDescentPrimaryHOneDirectLimit318
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
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318

open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFiniteLevelSurjectivity318 ActualTwoDescentHigherCohomologyDirectedMaps318
open ActualTwoDescentHigherCohomologyDirectedSystem318 ActualTwoDescentPrimaryClassEventualEquality318

abbrev higherHOneLimit (n : F) (hn : n ≠ 0) :=
  DirectLimit (fun k => continuousPowerHOne n hn k) (higherCohomologyMap n hn)

def primaryHOneLimitMap (n : F) (hn : n ≠ 0) : higherHOneLimit n hn →+ continuousPrimaryHOne n hn where
  toFun := DirectLimit.lift (higherCohomologyMap n hn) (fun i => powerIntoPrimaryHOne n hn i)
    (fun i j h x => (actual_power_primary_compatible n hn i j h x).symm)
  map_zero' := DirectLimit.lift_zero (fun i => powerIntoPrimaryHOne n hn i)
    (fun i j h x => (actual_power_primary_compatible n hn i j h x).symm)
  map_add' x y := DirectLimit.lift_add (fun i => powerIntoPrimaryHOne n hn i)
    (fun i j h x => (actual_power_primary_compatible n hn i j h x).symm) x y

lemma actual_primary_limit_surjective (n : F) (hn : n ≠ 0) : Function.Surjective (primaryHOneLimitMap n hn) := by
  intro x
  obtain ⟨k,y,hy⟩ := actual_primary_hone_finite_level n hn x
  exact ⟨⟦⟨k,y⟩⟧,hy⟩

lemma actual_primary_limit_injective (n : F) (hn : n ≠ 0) : Function.Injective (primaryHOneLimitMap n hn) := by
  intro x y h
  apply sub_eq_zero.mp
  have hz : primaryHOneLimitMap n hn (x-y)=0 := by rw [map_sub,h,sub_self]
  obtain ⟨i,z,he⟩ := DirectLimit.exists_eq_mk (x-y)
  rw [he] at hz ⊢
  obtain ⟨j,hij,hj⟩ := actual_primary_class_eventual_zero n hn i z hz
  exact (DirectLimit.exists_eq_zero _).mpr ⟨j,hij,hj⟩

/-- Actual continuous H1(E[2∞]) is the genuine direct limit of the actual higher crossed-cocycle quotients. -/
def primaryHOneLimitEquiv (n : F) (hn : n ≠ 0) : higherHOneLimit n hn ≃+ continuousPrimaryHOne n hn :=
  AddEquiv.ofBijective (primaryHOneLimitMap n hn) ⟨actual_primary_limit_injective n hn,actual_primary_limit_surjective n hn⟩

end ActualTwoDescentPrimaryHOneDirectLimit318
