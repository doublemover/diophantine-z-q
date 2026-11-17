module
public import ActualTwoDescentGoodPrimeKummerSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentLocalPointImageBridge318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentLiteralKummerClasses318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentExceptionalLocalPoints318
variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

lemma actual_local_point_kummer_image (n β : ℕ) (hn : n ≠ 0) (hβ : β ≠ 0)
    (P : LocalKummerPoint (p:=p) β n) :
    ∃ Q : Point (n : ℚ_[p]), kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) Q=
      retainedBetaClass (β : ℚ_[p]) (Nat.cast_ne_zero.mpr hβ) := by
  let hnq : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let hbq : (β : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hβ
  let h := curve_nonsingular (n : ℚ_[p]) P.point.x P.point.y hnq P.point.curve
  refine ⟨.some P.point.x P.point.y h,?_⟩
  have hp := (actual_kummer_pair_iff (n : ℚ_[p]) P.point.x P.point.y (β : ℚ_[p]) 1
    hnq h P.point.plus_ne P.point.minus_ne hbq one_ne_zero).mpr
    ⟨P.u,P.v,P.u_ne,P.v_ne,P.first,by simpa only [one_mul] using P.second⟩
  simpa only [class_of_one,retainedBetaClass] using hp

lemma actual_real_beta_image (n β : ℕ) (hn : n ≠ 0) (hβ : β ≠ 0) :
    ∃ Q : Point (n : ℝ), kummerClass (n : ℝ) (Nat.cast_ne_zero.mpr hn) Q=
      retainedBetaClass (β : ℝ) (Nat.cast_ne_zero.mpr hβ) := by
  obtain ⟨x,y,u,v,hx,hu,hv,hcurve,hA,hB⟩ := actual_real_kummer_point β n (Nat.pos_of_ne_zero hβ)
  have hnq : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hbq : (β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hβ
  have h := curve_nonsingular (n : ℝ) x y hnq hcurve
  have hA0 : x+3*n ≠ 0 := by rw [hA]; exact mul_ne_zero hbq (pow_ne_zero _ hu)
  have hB0 : x-n ≠ 0 := by rw [hB]; exact pow_ne_zero _ hv
  refine ⟨.some x y h,?_⟩
  have hp := (actual_kummer_pair_iff (n : ℝ) x y (β : ℝ) 1 hnq h hA0 hB0 hbq one_ne_zero).mpr
    ⟨u,v,hu,hv,hA,by simpa only [one_mul] using hB⟩
  simpa only [class_of_one,retainedBetaClass] using hp

end ActualTwoDescentLocalPointImageBridge318
