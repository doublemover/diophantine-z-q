module
public import ActualTwoDescentPowerTorsionBoundaries318
public section
noncomputable section
namespace ActualTwoDescentHigherDivisionCocycle318
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

open ActualTwoDescentGeometricDivisionTower318 ActualTwoDescentPowerValuedCocycles318
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentFullBoundaryHom318

/-- The actual division-point boundary is E[2^k]-valued because the multiple is the same rational point. -/
def divisionCocycle (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n)
    (Q : Point (algebraMap F Qbar n)) (hQ : (2^k) • Q=rationalPointMap n hn P) : powerValuedCocycles n hn k := by
  refine ⟨fullBoundary n hn Q,?_⟩
  intro σ
  change (2^k) • halfDifference n hn Q σ=0
  rw [←actual_difference_nsmul,hQ,halfDifference,actual_rational_point_fixed,sub_self]

def higherKummer (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n) : continuousPowerHOne n hn k :=
  powerClass n hn k (divisionCocycle n hn k P
    (geometricDivision n hn (rationalPointMap n hn P) k)
    (actual_geometric_division_power n hn (rationalPointMap n hn P) k))

end ActualTwoDescentHigherDivisionCocycle318
