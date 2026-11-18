module
public import ActualTwoDescentHigherShaStep318
public section
noncomputable section
namespace ActualTwoDescentHigherRationalStep318
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

open ActualTwoDescentGeometricDivisionTower318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentHigherDivisionChoice318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherCohomologyStep318

/-- The rational transition is multiplication by TWO, not the identity: this scalar is retained in the actual coefficient-inclusion square. -/
lemma actual_higher_kummer_step (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    higherCohomologyStep n hn k (higherKummerHom n hn k P)=higherKummerHom n hn (k+1) (2 • P) := by
  let Q := geometricDivision n hn (rationalPointMap n hn P) k
  have hQ : (2^k) • Q=rationalPointMap n hn P := actual_geometric_division_power n hn _ k
  have hQnext : (2^(k+1)) • Q=rationalPointMap n hn (2 • P) := by
    rw [pow_succ,Nat.mul_comm,mul_smul,hQ,map_nsmul]
  change higherCohomologyStep n hn k (powerClass n hn k (divisionCocycle n hn k P Q hQ))=
    higherKummer n hn (k+1) (2 • P)
  rw [actual_higher_kummer_of_division n hn (k+1) (2 • P) Q hQnext]
  rfl

end ActualTwoDescentHigherRationalStep318
