module
public import ActualTwoDescentHigherTransitionKernel318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerTransitionKernel318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerStep318
open ActualTwoDescentHigherRationalImage318 ActualTwoDescentHigherTransitionKernel318

/-- Exact transition kernel inside the actual all-place Selmer group, with the same rational2-torsion point. -/
theorem actual_higher_selmer_step_kernel (n : ℚ) (hn : n ≠ 0) (k : ℕ) (x : actualHigherSelmer n hn k) :
    higherSelmerStep n hn k x=0 ↔ ∃ P : Point n, 2 • P=0 ∧ higherRationalHom n hn k P=x := by
  constructor
  · intro hx
    obtain ⟨P,hP,he⟩ := (actual_higher_transition_kernel n hn k x.val).mp (congrArg Subtype.val hx)
    exact ⟨P,hP,Subtype.ext he⟩
  · rintro ⟨P,hP,rfl⟩
    apply Subtype.ext
    exact (actual_higher_transition_kernel n hn k _).mpr ⟨P,hP,rfl⟩

end ActualTwoDescentHigherSelmerTransitionKernel318
