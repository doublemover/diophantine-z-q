module
public import ActualTwoDescentHigherTorsionStep318
public section
noncomputable section
namespace ActualTwoDescentHigherCohomologyStep318
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

open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherTorsionStep318
open ActualTwoDescentHigherFullClassMap318

/-- Actual coefficient inclusion E[2^k]→E[2^(k+1)] induces this cohomology transition. No injectivity is presumed. -/
def higherCohomologyStep (n : F) (hn : n ≠ 0) (k : ℕ) : continuousPowerHOne n hn k →+ continuousPowerHOne n hn (k+1) :=
  QuotientAddGroup.lift _ ((powerClass n hn (k+1)).comp (higherCocycleStep n hn k)) (by
    rintro z ⟨T,rfl⟩
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨higherTorsionStep n k T,rfl⟩)

lemma actual_higher_step_full_class (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    higherFullClass n hn (k+1) (higherCohomologyStep n hn k x)=higherFullClass n hn k x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

end ActualTwoDescentHigherCohomologyStep318
