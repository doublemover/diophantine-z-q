module
public import ActualTwoDescentHigherSelmerCardinality318
public section
noncomputable section
namespace ActualTwoDescentPrimaryShaPowerEquivalence318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentHigherFullLifting318 ActualTwoDescentGeometricPowerTorsion318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

open ActualTwoDescentActualShaPower318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaDefinition318
open ActualTwoDescentPrimaryPowerLevels318

def primaryShaPowerHom (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    powerLevel (actualShaPrimary n hn) k →* Multiplicative (actualShaPower n hn k) where
  toFun x := Multiplicative.ofAdd ⟨(primaryShaInclusion n hn x.val).toAdd,x.val.val.toAdd.property,by
    have h := congrArg (primaryShaInclusion n hn) x.property
    have ha := congrArg Multiplicative.toAdd h
    simpa only [map_pow,map_one,Multiplicative.toAdd_pow,Multiplicative.toAdd_one] using ha⟩
  map_one' := rfl
  map_mul' x y := rfl

lemma actual_primary_sha_power_injective (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Function.Injective (primaryShaPowerHom n hn k) := by
  intro x y h
  apply Subtype.ext
  apply actual_primary_sha_inclusion_injective n hn
  exact congrArg (fun z : Multiplicative (actualShaPower n hn k) => Multiplicative.ofAdd z.toAdd.val) h

lemma actual_primary_sha_power_surjective (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Function.Surjective (primaryShaPowerHom n hn k) := by
  intro x
  let g : Multiplicative (actualSha n hn) := Multiplicative.ofAdd ⟨x.toAdd.val,x.toAdd.property.1⟩
  have hg : g^(2^k)=1 := by
    apply actual_full_sha_inclusion_injective n hn
    change Multiplicative.ofAdd ((2^k) • x.toAdd.val)=Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd x.toAdd.property.2
  let y : actualShaPrimary n hn := ⟨g,⟨k,hg⟩⟩
  exact ⟨⟨y,Subtype.ext hg⟩,rfl⟩

def primaryShaPowerEquiv (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    powerLevel (actualShaPrimary n hn) k ≃* Multiplicative (actualShaPower n hn k) :=
  MulEquiv.ofBijective (primaryShaPowerHom n hn k) ⟨actual_primary_sha_power_injective n hn k,actual_primary_sha_power_surjective n hn k⟩

end ActualTwoDescentPrimaryShaPowerEquivalence318
