module
public import ActualTwoDescentOddIntegralSquareLift318
public section
noncomputable section
namespace ActualTwoDescentIntegralPointLiftData318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] [NeZero (3 : ZMod p)]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

lemma integer_ne_of_residue {a : ℤ} (ha : (a : ZMod p) ≠ 0) : a ≠ 0 := by
  intro h
  exact ha (by rw [h,Int.cast_zero])

lemma padic_ne_of_residue {a : ℤ} (ha : (a : ZMod p) ≠ 0) : (a : ℚ_[p]) ≠ 0 :=
  Int.cast_ne_zero.mpr (integer_ne_of_residue ha)

/-- An actual local elliptic lift with literal integral adjusted Kummer coordinates.
The residues are compared by ring reduction, never by a nonexistent field map Q_p→F_p. -/
structure IntegralPointLift (n : ℤ) (hn : (n : ZMod p) ≠ 0) (P : Point (n : ZMod p)) where
  point : Point (n : ℚ_[p])
  A : ℤ
  B : ℤ
  first : rootCoordinate (firstRoot (n : ℚ_[p]) (padic_ne_of_residue hn)) point=(A : ℚ_[p])
  second : rootCoordinate (secondRoot (n : ℚ_[p]) (padic_ne_of_residue hn)) point=(B : ℚ_[p])
  first_residue : (A : ZMod p)=rootCoordinate (firstRoot (n : ZMod p) hn) P
  second_residue : (B : ZMod p)=rootCoordinate (secondRoot (n : ZMod p) hn) P

lemma actual_lift_first_unit (n : ℤ) (hn : (n : ZMod p) ≠ 0) (P : Point (n : ZMod p))
    (L : IntegralPointLift n hn P) : (L.A : ZMod p) ≠ 0 := by
  rw [L.first_residue]
  exact root_coordinate_nonzero _ _

lemma actual_lift_second_unit (n : ℤ) (hn : (n : ZMod p) ≠ 0) (P : Point (n : ZMod p))
    (L : IntegralPointLift n hn P) : (L.B : ZMod p) ≠ 0 := by
  rw [L.second_residue]
  exact root_coordinate_nonzero _ _

end ActualTwoDescentIntegralPointLiftData318
