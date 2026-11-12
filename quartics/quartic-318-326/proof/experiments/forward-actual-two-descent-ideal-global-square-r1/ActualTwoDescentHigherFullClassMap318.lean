module
public import ActualTwoDescentHigherKummerKernelReverse318
public section
noncomputable section
namespace ActualTwoDescentHigherFullClassMap318
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

def powerFullClass (n : F) (hn : n ≠ 0) (k : ℕ) : powerValuedCocycles n hn k →+ H1 (fullEllipticRep n hn) :=
  (fullClassHom n hn).comp (powerValuedCocycles n hn k).subtype

def higherFullClass (n : F) (hn : n ≠ 0) (k : ℕ) : continuousPowerHOne n hn k →+ H1 (fullEllipticRep n hn) :=
  QuotientAddGroup.lift _ (powerFullClass n hn k) (by
    rintro z ⟨T,rfl⟩
    exact actual_full_boundary_zero n hn T.val)

lemma actual_higher_full_kummer_zero (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    higherFullClass n hn k (higherKummerHom n hn k P)=0 :=
  actual_full_boundary_zero n hn _

lemma actual_higher_full_annihilated (n : F) (hn : n ≠ 0) (k : ℕ) (x : continuousPowerHOne n hn k) :
    (2^k) • higherFullClass n hn k x=0 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective x
  change (2^k) • fullClassHom n hn z.val=0
  rw [←map_nsmul]
  have hz : (2^k) • z.val=0 := by
    apply Subtype.ext; apply Subtype.ext; funext σ
    exact z.property σ
  rw [hz,map_zero]

end ActualTwoDescentHigherFullClassMap318
