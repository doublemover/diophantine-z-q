module
public import ActualTwoDescentHigherDivisionChoice318
public section
noncomputable section
namespace ActualTwoDescentHigherKummerHom318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentHigherDivisionChoice318 ActualTwoDescentFullBoundaryHom318

lemma actual_higher_kummer_add (n : F) (hn : n ≠ 0) (k : ℕ) (P R : Point n) :
    higherKummer n hn k (P+R)=higherKummer n hn k P+higherKummer n hn k R := by
  let Q := geometricDivision n hn (rationalPointMap n hn P) k
  let S := geometricDivision n hn (rationalPointMap n hn R) k
  have hQ : (2^k) • Q=rationalPointMap n hn P := actual_geometric_division_power n hn _ k
  have hS : (2^k) • S=rationalPointMap n hn R := actual_geometric_division_power n hn _ k
  have hQS : (2^k) • (Q+S)=rationalPointMap n hn (P+R) := by rw [nsmul_add,hQ,hS,map_add]
  rw [actual_higher_kummer_of_division n hn k (P+R) (Q+S) hQS,
    actual_higher_kummer_of_division n hn k P Q hQ,actual_higher_kummer_of_division n hn k R S hS,←map_add]
  congr 1
  apply Subtype.ext
  exact actual_full_boundary_add n hn Q S

def higherKummerHom (n : F) (hn : n ≠ 0) (k : ℕ) : Point n →+ continuousPowerHOne n hn k where
  toFun := higherKummer n hn k
  map_zero' := by
    have h := actual_higher_kummer_add n hn k 0 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' := actual_higher_kummer_add n hn k

end ActualTwoDescentHigherKummerHom318
