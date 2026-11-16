module
public import ActualTwoDescentFieldHalvingChoiceIndependence318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisConnectingHom318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_halving_cocycle_add (n : F) (hn : n ≠ 0) (P R : Point n) :
    rationalHalvingCocycle n hn (P+R)=rationalHalvingCocycle n hn P*rationalHalvingCocycle n hn R := by
  let Q := actualHalf n hn (rationalPointMap n hn P)
  let S := actualHalf n hn (rationalPointMap n hn R)
  have hQ : Q+Q=rationalPointMap n hn P := actual_half_spec n hn _
  have hS : S+S=rationalPointMap n hn R := actual_half_spec n hn _
  have hsum : (Q+S)+(Q+S)=rationalPointMap n hn (P+R) := by
    calc
      _=(Q+Q)+(S+S) := by abel
      _=_ := by rw [hQ,hS,map_add]
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  change ((rationalHalvingCocycle n hn (P+R) σ).toAdd : Point _)=
    ((rationalHalvingCocycle n hn P σ).toAdd : Point _)+((rationalHalvingCocycle n hn R σ).toAdd : Point _)
  rw [actual_halving_cocycle_evaluate n hn (P+R) (Q+S) hsum,
    actual_halving_cocycle_evaluate n hn P Q hQ,actual_halving_cocycle_evaluate n hn R S hS]
  simp only [halfDifference,map_add]
  abel

/-- A genuine connecting homomorphism constructed from actual algebraic half-points. -/
def galoisConnectingHom (n : F) (hn : n ≠ 0) :
    Multiplicative (Point n) →* (GalQ →* Multiplicative (closedTwoTorsion n)) where
  toFun P := rationalHalvingCocycle n hn P.toAdd
  map_one' := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    change ((rationalHalvingCocycle n hn 0 σ).toAdd : Point _)=0
    rw [actual_halving_cocycle_evaluate n hn 0 0 (by simp)]
    simp only [halfDifference,map_zero,sub_self]
  map_mul' P R := actual_halving_cocycle_add n hn P.toAdd R.toAdd

end ActualTwoDescentFieldGaloisConnectingHom318
