module
public import ActualTwoDescentPrimaryHOneNativeInjection318
public section
noncomputable section
namespace ActualTwoDescentRationalPrimaryTransition318
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

open ActualTwoDescentGeometricDivisionTower318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentHigherDivisionChoice318 ActualTwoDescentHigherCohomologyDirectedMaps318
open ActualTwoDescentHigherCohomologyDirectedSystem318

lemma actual_higher_kummer_directed (n : F) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) (P : Point n) :
    higherCohomologyMap n hn i j h (higherKummerHom n hn i P)=higherKummerHom n hn j ((2^(j-i)) • P) := by
  let Q := geometricDivision n hn (rationalPointMap n hn P) i
  have hQ : (2^i) • Q=rationalPointMap n hn P := actual_geometric_division_power n hn _ i
  have he : 2^j=2^(j-i)*2^i := by rw [←pow_add,Nat.sub_add_cancel h]
  have hQj : (2^j) • Q=rationalPointMap n hn ((2^(j-i)) • P) := by rw [he,mul_smul,hQ,map_nsmul]
  change higherCohomologyMap n hn i j h (powerClass n hn i (divisionCocycle n hn i P Q hQ))=higherKummer n hn j _
  rw [actual_higher_kummer_of_division n hn j _ Q hQj]
  rfl

def rationalPrimaryHom (n : ℚ) (hn : n ≠ 0) (k : ℕ) : Point n →+ actualPrimarySelmer n hn :=
  (higherSelmerIntoPrimary n hn k).comp (higherRationalHom n hn k)

lemma actual_rational_primary_transition (n : ℚ) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) (P : Point n) :
    rationalPrimaryHom n hn i P=rationalPrimaryHom n hn j ((2^(j-i)) • P) := by
  apply Subtype.ext
  change powerIntoPrimaryHOne n hn i (higherKummerHom n hn i P)=_
  rw [←actual_power_primary_compatible n hn i j h,actual_higher_kummer_directed]
  rfl

end ActualTwoDescentRationalPrimaryTransition318
