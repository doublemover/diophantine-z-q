module
public import ActualTwoDescentHigherSelmerToSha318
public section
noncomputable section
namespace ActualTwoDescentHigherRationalImage318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerShaComparison318
open ActualTwoDescentHigherSelmerToSha318 ActualTwoDescentActualShaDefinition318

lemma actual_higher_rational_in_selmer (n : ℚ) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    higherKummerHom n hn k P ∈ actualHigherSelmer n hn k := by
  apply (actual_higher_selmer_iff_sha n hn k _).mpr
  rw [actual_higher_full_kummer_zero]
  exact (actualSha n hn).zero_mem

def higherRationalHom (n : ℚ) (hn : n ≠ 0) (k : ℕ) : Point n →+ actualHigherSelmer n hn k where
  toFun P := ⟨higherKummerHom n hn k P,actual_higher_rational_in_selmer n hn k P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P Q)

lemma actual_higher_selmer_sha_kernel (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    (higherSelmerToSha n hn k).ker=(higherRationalHom n hn k).range := by
  ext x
  change higherSelmerToSha n hn k x=0 ↔ _
  constructor
  · intro hx
    obtain ⟨P,hP⟩ := (actual_higher_full_kernel n hn k x.val).mp (congrArg Subtype.val hx)
    exact ⟨P,Subtype.ext hP⟩
  · rintro ⟨P,rfl⟩
    exact Subtype.ext (actual_higher_full_kummer_zero n hn k P)

end ActualTwoDescentHigherRationalImage318
