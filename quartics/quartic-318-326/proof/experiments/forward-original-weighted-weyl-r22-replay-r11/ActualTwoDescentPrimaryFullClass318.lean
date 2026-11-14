module
public import ActualTwoDescentPrimaryHOneDirectLimit318
public section
noncomputable section
namespace ActualTwoDescentPrimaryFullClass318
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
open ActualTwoDescentFiniteLevelIntoPrimary318 ActualTwoDescentPrimaryFiniteLevelSurjectivity318

def primaryFullCocycleClass (n : F) (hn : n ≠ 0) : primaryCocycles n hn →+ H1 (fullEllipticRep n hn) :=
  (fullClassHom n hn).comp (primaryCocycles n hn).subtype

def primaryFullClass (n : F) (hn : n ≠ 0) : continuousPrimaryHOne n hn →+ H1 (fullEllipticRep n hn) :=
  QuotientAddGroup.lift _ (primaryFullCocycleClass n hn) (by
    rintro z ⟨T,rfl⟩
    exact actual_full_boundary_zero n hn T.val)

lemma actual_primary_full_finite_level (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    primaryFullClass n hn (powerIntoPrimaryHOne n hn k x)=higherFullClass n hn k x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- The actual primary cohomology maps onto exactly the primary torsion in actual continuous full elliptic H1. -/
theorem actual_primary_full_range (n : F) (hn : n ≠ 0) (x : H1 (fullEllipticRep n hn)) :
    x ∈ (primaryFullClass n hn).range ↔ x ∈ continuousFullHOne n hn ∧ ∃ k : ℕ, (2^k) • x=0 := by
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨k,y,rfl⟩ := actual_primary_hone_finite_level n hn z
    rw [actual_primary_full_finite_level]
    have h := (actual_higher_full_range n hn k _).mp ⟨y,rfl⟩
    exact ⟨h.1,⟨k,h.2⟩⟩
  · rintro ⟨hx,k,hk⟩
    obtain ⟨y,hy⟩ := (actual_higher_full_range n hn k x).mpr ⟨hx,hk⟩
    exact ⟨powerIntoPrimaryHOne n hn k y,(actual_primary_full_finite_level n hn k y).trans hy⟩

end ActualTwoDescentPrimaryFullClass318
