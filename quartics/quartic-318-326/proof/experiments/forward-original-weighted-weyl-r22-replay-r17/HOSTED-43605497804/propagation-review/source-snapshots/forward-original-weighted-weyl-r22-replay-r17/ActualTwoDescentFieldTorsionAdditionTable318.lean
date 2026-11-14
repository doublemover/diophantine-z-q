module
public import ActualTwoDescentFieldHalfFlipTranslations318
public section
noncomputable section
namespace ActualTwoDescentFieldTorsionAdditionTable318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

lemma actual_first_last_sum (n : K) (hn : n ≠ 0) : firstTorsion n hn+torsionPoint n hn=zeroTorsion n hn := by
  have hx : n ≠ -3*n := by intro h; apply hn; linear_combination h/4
  unfold firstTorsion torsionPoint zeroTorsion point
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx,WeierstrassCurve.Affine.slope_of_X_ne hx]
  congr 1
  · dsimp [WeierstrassCurve.Affine.addX,curve]
    simp only [sub_zero,zero_div,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero]
    ring
  · rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY]
    simp only [sub_zero,zero_div,zero_mul,zero_sub,neg_zero]

lemma actual_zero_torsion_double (n : K) (hn : n ≠ 0) : zeroTorsion n hn+zeroTorsion n hn=0 := by
  unfold zeroTorsion point
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [curve_negY]; ring
lemma actual_first_torsion_double (n : K) (hn : n ≠ 0) : firstTorsion n hn+firstTorsion n hn=0 := by
  unfold firstTorsion point
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [curve_negY]; ring

lemma actual_zero_first_sum (n : K) (hn : n ≠ 0) : zeroTorsion n hn+firstTorsion n hn=torsionPoint n hn := by
  rw [←actual_first_last_sum n hn]
  calc
    _=(firstTorsion n hn+firstTorsion n hn)+torsionPoint n hn := by abel
    _=torsionPoint n hn := by rw [actual_first_torsion_double,zero_add]
lemma actual_zero_last_sum (n : K) (hn : n ≠ 0) : zeroTorsion n hn+torsionPoint n hn=firstTorsion n hn := by
  rw [←actual_first_last_sum n hn]
  calc
    _=firstTorsion n hn+(torsionPoint n hn+torsionPoint n hn) := by abel
    _=firstTorsion n hn := by rw [actual_torsion_double_zero,add_zero]

end ActualTwoDescentFieldTorsionAdditionTable318
