module
public import ActualTwoDescentExceptionalPointLifts318
public section
noncomputable section
namespace ActualTwoDescentNonexceptionalPointLift318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentFiniteKummerAffineCoordinates318 ActualTwoDescentIntegralPointLiftData318
open ActualTwoDescentOddIntegralSquareLift318
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] [NeZero (3 : ZMod p)]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Lift the ordinate of an actual nonexceptional residue point, keeping its literal integral abscissa. -/
def nonexceptionalLift (hp2 : p ≠ 2) (n : ℤ) (hn : (n : ZMod p) ≠ 0)
    (x y : ZMod p) (h : (curve (n : ZMod p)).toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hB : x-(n : ZMod p) ≠ 0) (hA : x+3*(n : ZMod p) ≠ 0) :
    IntegralPointLift n hn (.some x y h) := by
  have hc := (curve_equation (n : ZMod p) x y).mp h.left
  have hy : y ≠ 0 := by
    intro hy
    rw [hy,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    exact (mul_ne_zero (mul_ne_zero hx hB) hA) hc.symm
  let X : ℤ := x.val
  have hX : (X : ZMod p)=x := by dsimp [X]; simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  have hC : y^2=((X*(X-n)*(X+3*n) : ℤ) : ZMod p) := by
    push_cast
    rw [hX]
    exact hc
  obtain ⟨r,hr,hr2⟩ := actual_odd_integral_square_lift hp2 (X*(X-n)*(X+3*n)) y hy hC
  have hcq : r^2=(X : ℚ_[p])*((X : ℚ_[p])-(n : ℚ_[p]))*((X : ℚ_[p])+3*(n : ℚ_[p])) := by
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_add,Int.cast_ofNat] using hr2
  have hAres : ((X+3*n : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,hX] using hA
  have hBres : ((X-n : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_sub,hX] using hB
  have hAq : (X : ℚ_[p])+3*(n : ℚ_[p]) ≠ 0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] using padic_ne_of_residue hAres
  have hBq : (X : ℚ_[p])-(n : ℚ_[p]) ≠ 0 := by
    simpa only [Int.cast_sub] using padic_ne_of_residue hBres
  refine {
    point := point (n : ℚ_[p]) (X : ℚ_[p]) r (padic_ne_of_residue hn) hcq
    A := X+3*n
    B := X-n
    first := ?_
    second := ?_
    first_residue := ?_
    second_residue := ?_ }
  · rw [point,actual_first_coordinate _ _ _ _ _ hAq]
    push_cast <;> rfl
  · rw [point,actual_second_coordinate _ _ _ _ _ hBq]
    push_cast <;> rfl
  · rw [actual_first_coordinate _ _ _ _ _ hA]
    push_cast
    rw [hX]
  · rw [actual_second_coordinate _ _ _ _ _ hB]
    push_cast
    rw [hX]

end ActualTwoDescentNonexceptionalPointLift318
