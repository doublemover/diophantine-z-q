module
public import ActualTwoDescentHigherDivisionCocycle318
public section
noncomputable section
namespace ActualTwoDescentHigherDivisionChoice318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentFullBoundaryHom318

lemma actual_division_choice_independent (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n)
    (Q R : Point (algebraMap F Qbar n)) (hQ : (2^k) • Q=rationalPointMap n hn P)
    (hR : (2^k) • R=rationalPointMap n hn P) :
    powerClass n hn k (divisionCocycle n hn k P Q hQ)=powerClass n hn k (divisionCocycle n hn k P R hR) := by
  apply sub_eq_zero.mp
  rw [←map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  let T : geometricPowerTorsion n k := ⟨Q-R,by change (2^k) • (Q-R)=0; rw [nsmul_sub,hQ,hR,sub_self]⟩
  refine ⟨T,?_⟩
  apply Subtype.ext
  exact map_sub (fullBoundaryHom n hn) Q R

lemma actual_higher_kummer_of_division (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n)
    (Q : Point (algebraMap F Qbar n)) (hQ : (2^k) • Q=rationalPointMap n hn P) :
    higherKummer n hn k P=powerClass n hn k (divisionCocycle n hn k P Q hQ) :=
  actual_division_choice_independent n hn k P _ Q _ hQ

end ActualTwoDescentHigherDivisionChoice318
