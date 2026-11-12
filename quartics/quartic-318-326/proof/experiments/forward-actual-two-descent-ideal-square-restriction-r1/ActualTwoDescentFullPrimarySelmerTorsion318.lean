module
public import ActualTwoDescentRationalPrimaryDivision318
public section
noncomputable section
namespace ActualTwoDescentFullPrimarySelmerTorsion318
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

open ActualTwoDescentPowerValuedCocycles318

lemma actual_higher_cohomology_annihilated (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    (2^k) • x=0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  change (2^k) • powerClass n hn k z=0
  rw [←map_nsmul]
  have hz : (2^k) • z=0 := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext σ
    exact z.property σ
  rw [hz,map_zero]

/-- Every element of the ACTUAL full primary Selmer group has actual2-power order. -/
lemma actual_primary_selmer_two_primary (n : ℚ) (hn : n ≠ 0) (x : actualPrimarySelmer n hn) :
    ∃ k : ℕ, (2^k) • x=0 := by
  obtain ⟨k,y,hy⟩ := actual_primary_selmer_finite_level n hn x
  refine ⟨k,?_⟩
  apply Subtype.ext
  change (2^k) • x.val=0
  rw [←hy,←map_nsmul,actual_higher_cohomology_annihilated,map_zero]

end ActualTwoDescentFullPrimarySelmerTorsion318
