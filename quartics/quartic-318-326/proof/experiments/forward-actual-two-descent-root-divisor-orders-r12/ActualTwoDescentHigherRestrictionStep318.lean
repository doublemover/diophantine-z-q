module
public import ActualTwoDescentHigherCohomologyStep318
public section
noncomputable section
namespace ActualTwoDescentHigherRestrictionStep318
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

open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherCohomologyStep318
open ActualTwoDescentHigherCohomologyRestriction318 ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]

/-- The same actual coefficient transition commutes with native closure/Galois restriction at every field map. -/
lemma actual_higher_step_restriction (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ)
    (x : continuousPowerHOne n hn k) :
    higherRestriction f n hn (k+1) (higherCohomologyStep n hn k x)=
      higherCohomologyStep (f n) (field_map_ne_zero f hn) k (higherRestriction f n hn k x) := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

end ActualTwoDescentHigherRestrictionStep318
