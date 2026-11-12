module
public import ActualTwoDescentPowerRepresentationClass318
public section
noncomputable section
namespace ActualTwoDescentContinuousPowerHOneInjection318
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

open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentPowerValuedCocycles318
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentPowerRepresentationClass318

/-- The continuous crossed-cocycle quotient embeds into ACTUAL Mathlib H1 of E[2^k]. -/
def continuousPowerIntoHOne (n : F) (hn : n ≠ 0) (k : ℕ) :
    continuousPowerHOne n hn k →+ H1 (powerTorsionRep n hn k) :=
  QuotientAddGroup.lift _ (powerMathlibClass n hn k) (by
    intro z hz
    exact (actual_power_mathlib_class_kernel n hn k z).mpr hz)

lemma actual_continuous_power_hone_injective (n : F) (hn : n ≠ 0) (k : ℕ) :
    Function.Injective (continuousPowerIntoHOne n hn k) := by
  intro x y h
  apply sub_eq_zero.mp
  have hx : continuousPowerIntoHOne n hn k (x-y)=0 := by rw [map_sub,h,sub_self]
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (x-y)
  rw [←hz] at hx
  have hm : z ∈ (powerBoundaryHom n hn k).range := (actual_power_mathlib_class_kernel n hn k z).mp hx
  exact hz.symm.trans ((QuotientAddGroup.eq_zero_iff z).mpr hm)

end ActualTwoDescentContinuousPowerHOneInjection318
