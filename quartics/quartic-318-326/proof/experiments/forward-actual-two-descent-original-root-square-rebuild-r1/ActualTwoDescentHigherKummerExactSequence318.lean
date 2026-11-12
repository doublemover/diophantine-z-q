module
public import ActualTwoDescentContinuousPowerHOneInjection318
public section
noncomputable section
namespace ActualTwoDescentHigherKummerExactSequence318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherKummerKernelReverse318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentContinuousPowerHOneInjection318

/-- Connected exact higher-power Kummer sequence with the actual continuous subgroup of genuine H1, for every k including0. -/
theorem actual_higher_kummer_exact_sequence (n : F) (hn : n ≠ 0) (k : ℕ) :
    (∀ P : Point n, higherKummerHom n hn k P=0 ↔ ∃ R : Point n, (2^k) • R=P) ∧
    (∀ x : continuousPowerHOne n hn k, higherFullClass n hn k x=0 ↔
      ∃ P : Point n, higherKummerHom n hn k P=x) ∧
    (∀ x : H1 (fullEllipticRep n hn), x ∈ (higherFullClass n hn k).range ↔
      x ∈ continuousFullHOne n hn ∧ (2^k) • x=0) ∧
    Function.Injective (continuousPowerIntoHOne n hn k) :=
  ⟨actual_higher_kummer_kernel n hn k,actual_higher_full_kernel n hn k,
    actual_higher_full_range n hn k,actual_continuous_power_hone_injective n hn k⟩

end ActualTwoDescentHigherKummerExactSequence318
