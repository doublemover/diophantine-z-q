module
public import ActualTwoDescentFieldTorsionAdditionTable318
public section
noncomputable section
namespace ActualTwoDescentFieldTorsionSignValues318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318 ActualTwoDescentFieldSquareOneUnits318
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The pair is ordered by the original roots(-3n,n), hence the original Kummer coordinates. -/
def torsionSignValue (n : K) (hn : n ≠ 0) (P : Point n) : SquareOne K × SquareOne K :=
  if P=0 then (1,1) else if P=zeroTorsion n hn then (negativeOne,negativeOne)
  else if P=firstTorsion n hn then (negativeOne,1) else (1,negativeOne)

lemma actual_torsion_distinct (n : K) (hn : n ≠ 0) :
    zeroTorsion n hn ≠ 0 ∧ firstTorsion n hn ≠ 0 ∧ torsionPoint n hn ≠ 0 ∧
    firstTorsion n hn ≠ zeroTorsion n hn ∧ torsionPoint n hn ≠ zeroTorsion n hn ∧ torsionPoint n hn ≠ firstTorsion n hn := by
  refine ⟨point_ne_zero _ _ _ _ _,point_ne_zero _ _ _ _ _,point_ne_zero _ _ _ _ _,?_,?_,?_⟩
  · intro h
    have hx : n=0 := (WeierstrassCurve.Affine.Point.some.inj h).1
    exact hn hx
  · intro h
    have hx : -3*n=0 := (WeierstrassCurve.Affine.Point.some.inj h).1
    apply hn; linear_combination -hx/3
  · intro h
    have hx : -3*n=n := (WeierstrassCurve.Affine.Point.some.inj h).1
    apply hn; linear_combination -hx/4

lemma actual_sign_zero (n : K) (hn : n ≠ 0) : torsionSignValue n hn 0=(1,1) := by simp [torsionSignValue]
lemma actual_sign_zero_torsion (n : K) (hn : n ≠ 0) : torsionSignValue n hn (zeroTorsion n hn)=(negativeOne,negativeOne) := by
  simp only [torsionSignValue,if_neg (actual_torsion_distinct n hn).1,if_pos rfl]
lemma actual_sign_first_torsion (n : K) (hn : n ≠ 0) : torsionSignValue n hn (firstTorsion n hn)=(negativeOne,1) := by
  simp only [torsionSignValue,if_neg (actual_torsion_distinct n hn).2.1,
    if_neg (actual_torsion_distinct n hn).2.2.2.1,if_pos rfl]
lemma actual_sign_last_torsion (n : K) (hn : n ≠ 0) : torsionSignValue n hn (torsionPoint n hn)=(1,negativeOne) := by
  simp only [torsionSignValue,if_neg (actual_torsion_distinct n hn).2.2.1,
    if_neg (actual_torsion_distinct n hn).2.2.2.2.1,if_neg (actual_torsion_distinct n hn).2.2.2.2.2]

end ActualTwoDescentFieldTorsionSignValues318
