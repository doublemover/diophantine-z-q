module
public import ActualTwoDescentGeometricDivisionTower318
public section
noncomputable section
namespace ActualTwoDescentGeometricPowerTorsion318
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

/-- Actual geometric2^k-torsion, not a trivial-action substitute. -/
def geometricPowerTorsion (n : F) (k : ℕ) : AddSubgroup (Point (algebraMap F Qbar n)) :=
  (nsmulAddMonoidHom (Point (algebraMap F Qbar n)) (2^k)).ker

lemma actual_power_torsion_galois (n : F) (hn : n ≠ 0) (k : ℕ) (σ : Gal)
    (P : geometricPowerTorsion n k) : (2^k) • galoisPointHom σ n hn P.val=0 := by
  rw [←map_nsmul]
  have h : (2^k) • P.val=0 := P.property
  rw [h,map_zero]

def powerTorsionAction (n : F) (hn : n ≠ 0) (k : ℕ) (σ : Gal) :
    geometricPowerTorsion n k →+ geometricPowerTorsion n k where
  toFun P := ⟨galoisPointHom σ n hn P.val,actual_power_torsion_galois n hn k σ P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

def powerTorsionRepresentation (n : F) (hn : n ≠ 0) (k : ℕ) : Representation ℤ Gal (geometricPowerTorsion n k) where
  toFun σ := (powerTorsionAction n hn k σ).toIntLinearMap
  map_one' := by ext P; exact Subtype.ext (actual_galois_one n hn P.val)
  map_mul' σ τ := by ext P; exact Subtype.ext (actual_galois_mul σ τ n hn P.val)

def powerTorsionRep (n : F) (hn : n ≠ 0) (k : ℕ) : Rep ℤ Gal := Rep.of (powerTorsionRepresentation n hn k)

end ActualTwoDescentGeometricPowerTorsion318
