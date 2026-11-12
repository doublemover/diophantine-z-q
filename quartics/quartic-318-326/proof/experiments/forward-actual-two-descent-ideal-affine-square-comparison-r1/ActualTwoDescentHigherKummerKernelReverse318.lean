module
public import ActualTwoDescentHigherKummerKernelForward318
public section
noncomputable section
namespace ActualTwoDescentHigherKummerKernelReverse318
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
open ActualTwoDescentHigherDivisionCocycle318 ActualTwoDescentHigherDivisionChoice318
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherKummerKernelForward318

lemma actual_higher_kummer_of_multiple (n : F) (hn : n ≠ 0) (k : ℕ) (R : Point n) :
    higherKummerHom n hn k ((2^k) • R)=0 := by
  have hR : (2^k) • rationalPointMap n hn R=rationalPointMap n hn ((2^k) • R) := (map_nsmul _ R _).symm
  change higherKummer n hn k ((2^k) • R)=0
  rw [actual_higher_kummer_of_division n hn k _ (rationalPointMap n hn R) hR]
  have hz : divisionCocycle n hn k _ (rationalPointMap n hn R) hR=0 :=
    Subtype.ext (actual_rational_boundary_zero n hn R)
  rw [hz,map_zero]

/-- Exact higher Kummer kernel for the actual rational group and actual continuous crossed-cocycle quotient. -/
theorem actual_higher_kummer_kernel (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    higherKummerHom n hn k P=0 ↔ ∃ R : Point n, (2^k) • R=P := by
  constructor
  · exact actual_higher_kummer_zero_implies_divisible n hn k P
  · rintro ⟨R,rfl⟩; exact actual_higher_kummer_of_multiple n hn k R

end ActualTwoDescentHigherKummerKernelReverse318
