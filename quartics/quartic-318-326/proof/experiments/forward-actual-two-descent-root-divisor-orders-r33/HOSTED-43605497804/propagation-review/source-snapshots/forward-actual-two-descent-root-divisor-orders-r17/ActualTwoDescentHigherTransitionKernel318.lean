module
public import ActualTwoDescentHigherRationalStep318
public section
noncomputable section
namespace ActualTwoDescentHigherTransitionKernel318
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
open ActualTwoDescentHigherCohomologyStep318 ActualTwoDescentHigherTorsionStep318
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherDivisionCocycle318 ActualTwoDescentHigherDivisionChoice318
open ActualTwoDescentHigherRationalStep318 ActualTwoDescentFullBoundaryHom318 ActualTwoDescentActualEllipticFieldMap318

/-- The actual cohomology transition kernel is the connecting image of rational TWO-torsion. It need not be injective. -/
theorem actual_higher_transition_kernel (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    higherCohomologyStep n hn k x=0 ↔ ∃ P : Point n, 2 • P=0 ∧ higherKummerHom n hn k P=x := by
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
    have hm : higherCocycleStep n hn k z ∈ (powerBoundaryHom n hn (k+1)).range :=
      (QuotientAddGroup.eq_zero_iff _).mp hx
    obtain ⟨T,hT⟩ := hm
    have he (σ : Gal) : halfDifference n hn T.val σ=z.val.val σ :=
      congrArg (fun w : powerValuedCocycles n hn (k+1) => w.val.val σ) hT
    have hfix (σ : Gal) : galoisPointHom σ n hn ((2^k) • T.val)=(2^k) • T.val := by
      apply sub_eq_zero.mp
      change halfDifference n hn ((2^k) • T.val) σ=0
      rw [actual_difference_nsmul,he]
      exact z.property σ
    obtain ⟨P,hP⟩ := actual_fixed_point_rational n hn ((2^k) • T.val) hfix
    refine ⟨P,?_,?_⟩
    · apply actual_elliptic_field_map_injective (algebraMap F Qbar) n hn
      change rationalPointMap n hn (2 • P)=rationalPointMap n hn 0
      rw [map_nsmul,hP,map_zero,←mul_smul,Nat.mul_comm,←pow_succ]
      exact T.property
    · change higherKummer n hn k P=powerClass n hn k z
      rw [actual_higher_kummer_of_division n hn k P T.val hP.symm]
      congr 1
      apply actual_power_cocycle_ext
      exact he
  · rintro ⟨P,hP,rfl⟩
    rw [actual_higher_kummer_step,hP,map_zero]

end ActualTwoDescentHigherTransitionKernel318
