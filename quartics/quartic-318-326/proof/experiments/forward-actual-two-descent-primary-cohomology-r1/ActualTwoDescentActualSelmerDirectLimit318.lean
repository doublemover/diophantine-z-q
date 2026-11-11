module
public import ActualTwoDescentHigherSelmerIntoPrimary318
public section
noncomputable section
namespace ActualTwoDescentActualSelmerDirectLimit318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherSelmerDirectedSystem318
open ActualTwoDescentHigherSelmerIntoPrimary318 ActualTwoDescentPrimaryClassEventualEquality318

abbrev higherSelmerLimit (n : ℚ) (hn : n ≠ 0) :=
  DirectLimit (fun k => actualHigherSelmer n hn k) (higherSelmerMap n hn)

def primarySelmerLimitMap (n : ℚ) (hn : n ≠ 0) : higherSelmerLimit n hn →+ actualPrimarySelmer n hn where
  toFun := DirectLimit.lift (higherSelmerMap n hn) (fun i => higherSelmerIntoPrimary n hn i)
    (fun i j h x => (actual_selmer_primary_compatible n hn i j h x).symm)
  map_zero' := DirectLimit.lift_zero (fun i => higherSelmerIntoPrimary n hn i)
    (fun i j h x => (actual_selmer_primary_compatible n hn i j h x).symm)
  map_add' x y := DirectLimit.lift_add (fun i => higherSelmerIntoPrimary n hn i)
    (fun i j h x => (actual_selmer_primary_compatible n hn i j h x).symm) x y

lemma actual_primary_selmer_limit_surjective (n : ℚ) (hn : n ≠ 0) : Function.Surjective (primarySelmerLimitMap n hn) := by
  intro x
  obtain ⟨k,y,hy⟩ := actual_primary_selmer_finite_level n hn x
  exact ⟨⟦⟨k,y⟩⟧,Subtype.ext hy⟩

lemma actual_primary_selmer_limit_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (primarySelmerLimitMap n hn) := by
  intro x y h
  apply sub_eq_zero.mp
  have hz : primarySelmerLimitMap n hn (x-y)=0 := by rw [map_sub,h,sub_self]
  obtain ⟨i,z,he⟩ := DirectLimit.exists_eq_mk (x-y)
  rw [he] at hz ⊢
  obtain ⟨j,hij,hj⟩ := actual_primary_class_eventual_zero n hn i z.val (congrArg Subtype.val hz)
  exact (DirectLimit.exists_eq_zero _).mpr ⟨j,hij,Subtype.ext hj⟩

/-- Genuine direct-limit identification with the actual full primary Selmer group. Noninjective finite-level transitions are handled by actual eventual equality. -/
def actualPrimarySelmerLimitEquiv (n : ℚ) (hn : n ≠ 0) : higherSelmerLimit n hn ≃+ actualPrimarySelmer n hn :=
  AddEquiv.ofBijective (primarySelmerLimitMap n hn) ⟨actual_primary_selmer_limit_injective n hn,actual_primary_selmer_limit_surjective n hn⟩

end ActualTwoDescentActualSelmerDirectLimit318
