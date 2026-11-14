module
public import ActualTwoDescentActualShaPower318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerToSha318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentHigherFullLifting318 ActualTwoDescentGeometricPowerTorsion318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerShaComparison318 ActualTwoDescentActualShaPower318

def higherSelmerToSha (n : ℚ) (hn : n ≠ 0) (k : ℕ) : actualHigherSelmer n hn k →+ actualShaPower n hn k where
  toFun x := ⟨higherFullClass n hn k x.val,(actual_higher_selmer_iff_sha n hn k x.val).mp x.property,
    actual_higher_full_annihilated n hn k x.val⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

/-- Every actual higher Sha torsion class is reached from the independently defined all-place higher Selmer group. -/
theorem actual_higher_selmer_sha_surjective (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Function.Surjective (higherSelmerToSha n hn k) := by
  rintro ⟨x,hSha,hk⟩
  obtain ⟨z,hz,hlocal⟩ := hSha
  have hzk : (2^k) • fullClassHom n hn z=0 := by rw [hz]; exact hk
  obtain ⟨w,hw⟩ := actual_higher_full_lift n hn k z hzk
  have he : higherFullClass n hn k (powerClass n hn k w)=x := hw.trans hz
  have hm : powerClass n hn k w ∈ actualHigherSelmer n hn k :=
    (actual_higher_selmer_iff_sha n hn k _).mpr (by rw [he]; exact ⟨z,hz,hlocal⟩)
  exact ⟨⟨powerClass n hn k w,hm⟩,Subtype.ext he⟩

end ActualTwoDescentHigherSelmerToSha318
