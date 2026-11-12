module
public import ActualTwoDescentPrimarySelmerShaExactSequence318
public section
noncomputable section
namespace ActualTwoDescentRationalPrimaryDivision318
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

open ActualTwoDescentRationalPrimaryTransition318 ActualTwoDescentActualPrimaryRationalImage318

lemma actual_rational_primary_half (n : ℚ) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    2 • rationalPrimaryHom n hn (k+1) P=rationalPrimaryHom n hn k P := by
  have h := actual_rational_primary_transition n hn k (k+1) (Nat.le_succ k) P
  have he : k+1-k=1 := by omega
  rw [he,pow_one,map_nsmul] at h
  exact h.symm

/-- The actual rational primary image is genuinely2-divisible, using the correct scalar-two transition. -/
theorem actual_rational_primary_two_surjective (n : ℚ) (hn : n ≠ 0) :
    Function.Surjective (nsmulAddMonoidHom (α:=rationalPrimaryImage n hn) 2) := by
  rintro ⟨x,k,P,rfl⟩
  exact ⟨⟨rationalPrimaryHom n hn (k+1) P,⟨k+1,P,rfl⟩⟩,
    Subtype.ext (actual_rational_primary_half n hn k P)⟩

end ActualTwoDescentRationalPrimaryDivision318
