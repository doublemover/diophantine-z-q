module
public import ActualTwoDescentAllResiduePointLifts318
public section
noncomputable section
namespace ActualTwoDescentLiftedKummerClasses318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentFiniteKummerHom318 ActualTwoDescentFiniteRootKummerHom318
open ActualTwoDescentIntegralPointLiftData318 ActualTwoDescentOddIntegralSquareLift318
open ActualTwoDescentSquareClassQuotient318
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] [NeZero (3 : ZMod p)]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Lifting the actual finite elliptic point lifts its literal pair of unit Kummer classes. -/
theorem actual_lift_kummer_classes (hp2 : p ≠ 2) (n a b : ℤ)
    (hn : (n : ZMod p) ≠ 0) (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (P : Point (n : ZMod p)) (L : IntegralPointLift n hn P)
    (H : kummerClass (n : ZMod p) hn P=(classOf (a : ZMod p) ha,classOf (b : ZMod p) hb)) :
    kummerClass (n : ℚ_[p]) (padic_ne_of_residue hn) L.point=
      (classOf (a : ℚ_[p]) (padic_ne_of_residue ha),classOf (b : ℚ_[p]) (padic_ne_of_residue hb)) := by
  have hA := actual_lift_first_unit n hn P L
  have hB := actual_lift_second_unit n hn P L
  have hfa : classOf (L.A : ZMod p) hA=classOf (a : ZMod p) ha := by
    rw [L.first_residue]
    exact congrArg Prod.fst H
  have hfb : classOf (L.B : ZMod p) hB=classOf (b : ZMod p) hb := by
    rw [L.second_residue]
    exact congrArg Prod.snd H
  obtain ⟨r,hr,hr2⟩ := actual_unit_squareclass_lift hp2 L.A a hA ha
    ((class_of_eq_iff _ _ _ _).mp hfa)
  obtain ⟨s,hs,hs2⟩ := actual_unit_squareclass_lift hp2 L.B b hB hb
    ((class_of_eq_iff _ _ _ _).mp hfb)
  apply Prod.ext
  · change classOf (rootCoordinate (firstRoot (n : ℚ_[p]) _) L.point) _=classOf (a : ℚ_[p]) _
    rw [L.first]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,hr2⟩
  · change classOf (rootCoordinate (secondRoot (n : ℚ_[p]) _) L.point) _=classOf (b : ℚ_[p]) _
    rw [L.second]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨s,hs,hs2⟩

end ActualTwoDescentLiftedKummerClasses318
