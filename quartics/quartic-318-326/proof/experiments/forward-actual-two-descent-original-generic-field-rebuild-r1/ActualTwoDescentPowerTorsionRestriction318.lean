module
public import ActualTwoDescentHigherKummerExactSequence318
public section
noncomputable section
namespace ActualTwoDescentPowerTorsionRestriction318
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

def powerTorsionTransport (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ) :
    geometricPowerTorsion n k →+ geometricPowerTorsion (f n) k where
  toFun T := ⟨closurePointMap f n hn T.val,by
    change (2^k) • closurePointMap f n hn T.val=0
    rw [←map_nsmul]
    have h : (2^k) • T.val=0 := T.property
    rw [h,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' T U := Subtype.ext (map_add _ T.val U.val)

def powerCocycleRestriction (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ) :
    powerValuedCocycles n hn k →+ powerValuedCocycles (f n) (field_map_ne_zero f hn) k where
  toFun z := ⟨fullCocycleRestriction f n hn z.val,by
    intro σ
    change (2^k) • closurePointMap f n hn (z.val.val (Field.absoluteGaloisGroup.map f σ))=0
    rw [←map_nsmul,z.property _,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ z.val w.val)

lemma actual_power_restriction_boundary (f : F →+* L) (n : F) (hn : n ≠ 0) (k : ℕ)
    (T : geometricPowerTorsion n k) :
    powerCocycleRestriction f n hn k (powerBoundaryHom n hn k T)=
      powerBoundaryHom (f n) (field_map_ne_zero f hn) k (powerTorsionTransport f n hn k T) :=
  Subtype.ext (actual_full_restriction_boundary f n hn T.val)

end ActualTwoDescentPowerTorsionRestriction318
