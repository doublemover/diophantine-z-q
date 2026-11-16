module
public import ActualTwoDescentHigherFullClassMap318
public section
noncomputable section
namespace ActualTwoDescentHigherFullKernel318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentHigherDivisionChoice318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentFullBoundaryHom318

/-- Exact higher Kummer sequence at continuous H1(E[2^k]): the kernel in full elliptic H1 is the actual rational Kummer image. -/
theorem actual_higher_full_kernel (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    higherFullClass n hn k x=0 ↔ ∃ P : Point n, higherKummerHom n hn k P=x := by
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
    have hz : fullClassHom n hn z.val=0 := hx
    obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn z.val).mp hz
    have hfix (σ : Gal) : galoisPointHom σ n hn ((2^k) • Q)=(2^k) • Q := by
      apply sub_eq_zero.mp
      change halfDifference n hn ((2^k) • Q) σ=0
      rw [actual_difference_nsmul,←hQ σ]
      exact z.property σ
    obtain ⟨P,hP⟩ := actual_fixed_point_rational n hn ((2^k) • Q) hfix
    refine ⟨P,?_⟩
    change higherKummer n hn k P=powerClass n hn k z
    rw [actual_higher_kummer_of_division n hn k P Q hP.symm]
    congr 1
    apply actual_power_cocycle_ext
    intro σ
    exact (hQ σ).symm
  · rintro ⟨P,rfl⟩
    exact actual_higher_full_kummer_zero n hn k P

end ActualTwoDescentHigherFullKernel318
