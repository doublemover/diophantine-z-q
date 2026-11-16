module
public import ActualTwoDescentPrimaryRepresentationClass318
public section
noncomputable section
namespace ActualTwoDescentPrimaryHOneNativeInjection318
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

open ActualTwoDescentPrimaryGeometricCocycles318 ActualTwoDescentPrimaryGeometricBoundary318
open ActualTwoDescentPrimaryTorsionRepresentation318 ActualTwoDescentPrimaryRepresentationClass318
open ActualTwoDescentActualPrimarySelmer318

def continuousPrimaryIntoHOne (n : F) (hn : n ≠ 0) : continuousPrimaryHOne n hn →+ H1 (primaryTorsionRep n hn) :=
  QuotientAddGroup.lift _ (primaryMathlibClass n hn) (by
    intro z hz
    exact (actual_primary_mathlib_kernel n hn z).mpr hz)

lemma actual_primary_hone_native_injective (n : F) (hn : n ≠ 0) : Function.Injective (continuousPrimaryIntoHOne n hn) := by
  intro x y h
  apply sub_eq_zero.mp
  have hx : continuousPrimaryIntoHOne n hn (x-y)=0 := by rw [map_sub,h,sub_self]
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (x-y)
  rw [←hz] at hx
  have hm : z ∈ (primaryBoundaryHom n hn).range := (actual_primary_mathlib_kernel n hn z).mp hx
  exact hz.symm.trans ((QuotientAddGroup.eq_zero_iff z).mpr hm)

/-- The actual full primary Selmer group is a subgroup of genuine Mathlib H1(E[2∞]), not a formal direct-limit label. -/
def primarySelmerIntoNativeHOne (n : ℚ) (hn : n ≠ 0) : actualPrimarySelmer n hn →+ H1 (primaryTorsionRep n hn) :=
  (continuousPrimaryIntoHOne n hn).comp (actualPrimarySelmer n hn).subtype

lemma actual_primary_selmer_native_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (primarySelmerIntoNativeHOne n hn) :=
  (actual_primary_hone_native_injective n hn).comp Subtype.val_injective

end ActualTwoDescentPrimaryHOneNativeInjection318
