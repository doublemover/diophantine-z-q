module
public import ActualTwoDescentRationalHeightDescent318
public section
noncomputable section
namespace ActualTwoDescentFourActualTorsionPoints318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318

def fourTorsion (n : ℚ) (hn : n ≠ 0) : Fin 4 → Point n :=
  ![0,zeroTorsion n hn,firstTorsion n hn,torsionPoint n hn]

lemma actual_four_torsion_double (n : ℚ) (hn : n ≠ 0) (i : Fin 4) :
    fourTorsion n hn i+fourTorsion n hn i=0 := by
  fin_cases i
  · simp [fourTorsion]
  all_goals
    simp only [fourTorsion,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [zeroTorsion,firstTorsion,torsionPoint,point]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    rw [curve_negY]
    ring

lemma actual_four_torsion_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (fourTorsion n hn) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [fourTorsion,zeroTorsion,firstTorsion,torsionPoint,point,WeierstrassCurve.Affine.Point.some.injEq]
  all_goals exfalso; apply hn; linarith

/-- All actual rational two-torsion points are exactly the four displayed
points on the original cubic. -/
theorem actual_two_torsion_exhaustion (n : ℚ) (hn : n ≠ 0) (P : Point n) (hP : P+P=0) :
    ∃ i : Fin 4, P=fourTorsion n hn i := by
  cases P with
  | zero => exact ⟨0,rfl⟩
  | some x y h =>
    have hy : y=0 := by
      by_contra hy
      have hy' : y ≠ (curve n).toAffine.negY x y := by rw [curve_negY]; intro he; apply hy; linarith
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy'] at hP
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hP
    have hc := (curve_equation n x y).mp h.left
    rw [hy,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    rcases mul_eq_zero.mp hc.symm with h01|h3
    · rcases mul_eq_zero.mp h01 with h0|h1
      · subst x; subst y; exact ⟨1,rfl⟩
      · have hx : x=n := sub_eq_zero.mp h1
        subst x; subst y; exact ⟨2,rfl⟩
    · have hx : x= -3*n := by linarith
      subst x; subst y; exact ⟨3,rfl⟩

end ActualTwoDescentFourActualTorsionPoints318
