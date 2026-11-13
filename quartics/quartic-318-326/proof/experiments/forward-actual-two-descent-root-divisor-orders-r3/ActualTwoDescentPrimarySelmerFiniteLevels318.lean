module
public import ActualTwoDescentActualPrimarySelmer318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerFiniteLevels318
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

open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentFiniteLevelIntoPrimary318 ActualTwoDescentPrimaryFiniteLevelSurjectivity318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerShaComparison318

lemma actual_primary_selmer_finite_level_iff (n : ℚ) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    powerIntoPrimaryHOne n hn k x ∈ actualPrimarySelmer n hn ↔ x ∈ actualHigherSelmer n hn k := by
  rw [actual_primary_selmer_iff_sha,actual_primary_full_finite_level,actual_higher_selmer_iff_sha]

/-- Every actual full primary Selmer class is represented in ONE actual higher Selmer group. The SAME level works at all places because local exactness uses full-H1 vanishing. -/
theorem actual_primary_selmer_finite_level (n : ℚ) (hn : n ≠ 0) (x : actualPrimarySelmer n hn) :
    ∃ k : ℕ, ∃ y : actualHigherSelmer n hn k, powerIntoPrimaryHOne n hn k y.val=x.val := by
  obtain ⟨k,y,hy⟩ := actual_primary_hone_finite_level n hn x.val
  have hm : y ∈ actualHigherSelmer n hn k :=
    (actual_primary_selmer_finite_level_iff n hn k y).mp (by rw [hy]; exact x.property)
  exact ⟨k,⟨y,hm⟩,hy⟩

end ActualTwoDescentPrimarySelmerFiniteLevels318
