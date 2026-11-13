module
public import ActualTwoDescentHigherSelmerTransitionKernel318
public section
noncomputable section
namespace ActualTwoDescentPrimaryGeometricCocycles318
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

abbrev geometricPrimary (n : F) := AddCommGroup.primaryComponent (Point (algebraMap F Qbar n)) 2

/-- Continuous crossed cocycles valued in the ACTUAL full geometric2-primary torsion subgroup. -/
def primaryCocycles (n : F) (hn : n ≠ 0) : AddSubgroup (continuousFullCocycles n hn) where
  carrier := {z | ∀ σ : Gal, z.val σ ∈ geometricPrimary n}
  zero_mem' σ := (geometricPrimary n).zero_mem
  add_mem' hz hw σ := (geometricPrimary n).add_mem (hz σ) (hw σ)
  neg_mem' hz σ := (geometricPrimary n).neg_mem (hz σ)

lemma actual_nsmul_power_mono {A : Type*} [AddCommGroup A] {x : A} {i j : ℕ}
    (hij : i ≤ j) (hx : (2^i) • x=0) : (2^j) • x=0 := by
  obtain ⟨a,ha⟩ := Nat.pow_dvd_pow 2 hij
  rw [ha,mul_comm,mul_smul,hx,nsmul_zero]

end ActualTwoDescentPrimaryGeometricCocycles318
