module
public import ActualTwoDescentIntegralPointLiftData318
public section
noncomputable section
namespace ActualTwoDescentExceptionalPointLifts318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentFiniteKummerAffineCoordinates318 ActualTwoDescentIntegralPointLiftData318
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] [NeZero (3 : ZMod p)]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

def infinityLift (n : ℤ) (hn : (n : ZMod p) ≠ 0) : IntegralPointLift n hn 0 where
  point := 0
  A := 1
  B := 1
  first := by simp only [rootCoordinate,Int.cast_one]
  second := by simp only [rootCoordinate,Int.cast_one]
  first_residue := by simp only [rootCoordinate,Int.cast_one]
  second_residue := by simp only [rootCoordinate,Int.cast_one]

def zeroRootLift (n : ℤ) (hn : (n : ZMod p) ≠ 0) (y : ZMod p)
    (h : (curve (n : ZMod p)).toAffine.Nonsingular 0 y) :
    IntegralPointLift n hn (.some 0 y h) where
  point := point (n : ℚ_[p]) 0 0 (padic_ne_of_residue hn) (by ring)
  A := 3*n
  B := -n
  first := by
    rw [point,actual_first_coordinate _ _ _ _ _ (by simpa only [zero_add] using
      mul_ne_zero (by norm_num : (3 : ℚ_[p]) ≠ 0) (padic_ne_of_residue hn))]
    push_cast <;> ring
  second := by
    rw [point,actual_second_coordinate _ _ _ _ _ (by simpa using neg_ne_zero.mpr (padic_ne_of_residue hn))]
    push_cast <;> ring
  first_residue := by
    rw [actual_first_coordinate _ _ _ _ _ (by simpa only [zero_add] using mul_ne_zero good_three_ne hn)]
    push_cast <;> ring
  second_residue := by
    rw [actual_second_coordinate _ _ _ _ _ (by simpa using neg_ne_zero.mpr hn)]
    push_cast <;> ring

def firstRootLift (n : ℤ) (hn : (n : ZMod p) ≠ 0) (y : ZMod p)
    (h : (curve (n : ZMod p)).toAffine.Nonsingular (n : ZMod p) y) :
    IntegralPointLift n hn (.some (n : ZMod p) y h) where
  point := point (n : ℚ_[p]) (n : ℚ_[p]) 0 (padic_ne_of_residue hn) (by ring)
  A := 4*n
  B := 4*n^2
  first := by
    rw [point,actual_first_coordinate _ _ _ _ _ (by
      intro he; apply mul_ne_zero (by norm_num : (4 : ℚ_[p]) ≠ 0) (padic_ne_of_residue hn); linear_combination he)]
    push_cast <;> ring
  second := by
    rw [point,actual_second_at_root]
    push_cast <;> ring
  first_residue := by
    rw [actual_first_coordinate _ _ _ _ _ (by intro he; apply mul_ne_zero good_four_ne hn; linear_combination he)]
    push_cast <;> ring
  second_residue := by
    rw [actual_second_at_root]
    push_cast <;> ring

def secondRootLift (n : ℤ) (hn : (n : ZMod p) ≠ 0) (y : ZMod p)
    (h : (curve (n : ZMod p)).toAffine.Nonsingular (-3*(n : ZMod p)) y) :
    IntegralPointLift n hn (.some (-3*(n : ZMod p)) y h) where
  point := point (n : ℚ_[p]) (-3*(n : ℚ_[p])) 0 (padic_ne_of_residue hn) (by ring)
  A := 12*n^2
  B := -4*n
  first := by
    rw [point,actual_first_at_root]
    push_cast <;> ring
  second := by
    rw [point,actual_second_coordinate _ _ _ _ _ (by
      intro he; apply mul_ne_zero (by norm_num : (4 : ℚ_[p]) ≠ 0) (padic_ne_of_residue hn); linear_combination -he)]
    push_cast <;> ring
  first_residue := by
    rw [actual_first_at_root]
    push_cast <;> ring
  second_residue := by
    rw [actual_second_coordinate _ _ _ _ _ (by intro he; apply mul_ne_zero good_four_ne hn; linear_combination -he)]
    push_cast <;> ring

end ActualTwoDescentExceptionalPointLifts318
