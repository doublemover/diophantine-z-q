module
public import ActualTwoDescentHalvingChoiceIndependence318
public section
noncomputable section
namespace ActualTwoDescentGaloisConnectingHom318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
open ActualTwoDescentGaloisTwoTorsion318 ActualTwoDescentHalvingCocycle318
open ActualTwoDescentHalvingChoiceIndependence318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_halving_cocycle_add (n : ℚ) (hn : n ≠ 0) (P R : Point n) :
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
def galoisConnectingHom (n : ℚ) (hn : n ≠ 0) :
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

end ActualTwoDescentGaloisConnectingHom318
