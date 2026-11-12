module
public import ActualTwoDescentQuotientCardinalitySurjectivity318
public section
noncomputable section
namespace ActualTwoDescentBetaNonexceptional318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentEightClassCube318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318 ActualTwoDescentSquareClassQuotient318
variable [DecidableEq K]

lemma actual_beta_not_torsion_cube (n b : K) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb)) (ε c : ZMod 2) :
    cubeClass n b hn hb (0,0,1) ≠ cubeClass n b hn hb (ε,c,0) := by
  intro he
  have hc := congrArg (fun v : Cube => v.2.2) (hi he)
  norm_num at hc

/-- An actual beta representative is automatically nonexceptional when the
whole cube is independent; hence it retains the original nonzero coordinates. -/
theorem actual_beta_nonexceptional (n b : K) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb)) (P : Point n)
    (H : kummerClass n hn P=cubeClass n b hn hb (0,0,1)) :
    ∃ x y : K, ∃ h : (curve n).toAffine.Nonsingular x y,
      P=.some x y h ∧ x ≠ 0 ∧ x-n ≠ 0 ∧ x+3*n ≠ 0 := by
  cases P with
  | zero =>
    exfalso
    apply actual_beta_not_torsion_cube n b hn hb hi 0 0
    rw [←H,kummer_class_zero]
    simp [cubeClass]
  | some x y h =>
    have hc := (curve_equation n x y).mp h.left
    have hx : x ≠ 0 := by
      intro he
      have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,he]
        ring
      subst x; subst y
      apply actual_beta_not_torsion_cube n b hn hb hi 1 1
      rw [←H]
      change kummerClass n hn (zeroTorsion n hn)=_
      rw [actual_zero_torsion_class]
      simp [cubeClass]
    have hB : x-n ≠ 0 := by
      intro he
      have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,he]
        ring
      have hx : x=n := sub_eq_zero.mp he
      subst x; subst y
      apply actual_beta_not_torsion_cube n b hn hb hi 0 1
      rw [←H]
      change kummerClass n hn (firstTorsion n hn)=_
      rw [actual_first_torsion_class]
      simp [cubeClass]
    have hA : x+3*n ≠ 0 := by
      intro he
      have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,he]
        ring
      have hx : x= -3*n := by linear_combination he
      subst x; subst y
      apply actual_beta_not_torsion_cube n b hn hb hi 1 0
      rw [←H]
      change kummerClass n hn (torsionPoint n hn)=_
      rw [actual_second_torsion_class]
      simp [cubeClass]
    exact ⟨x,y,h,rfl,hx,hB,hA⟩

end ActualTwoDescentBetaNonexceptional318
