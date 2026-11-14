module
public import ActualTwoDescentFiniteKummerAffineCoordinates318
public section
noncomputable section
namespace ActualTwoDescentFiniteExceptionalHalvingRoots318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteSimpleRootCoordinates318
open ActualTwoDescentFiniteKummerHom318 ActualTwoDescentFiniteKummerAffineCoordinates318
variable [DecidableEq K]

/-- At every finite two-torsion point, identity Kummer class still produces
all three actual roots required for the SAME halving formula. -/
theorem actual_exceptional_halving_roots (n x y : K) (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (H : kummerClass n hn (.some x y h)=1)
    (he : x=0 ∨ x=n ∨ x= -3*n) :
    ∃ a b c : K, a^2=x ∧ b^2=x-n ∧ c^2=x+3*n ∧ a*b*c= -y := by
  have hc := (curve_equation n x y).mp h.left
  have hy : y=0 := by
    apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rcases he with hx|hx|hx <;> rw [hc,hx] <;> ring
  obtain ⟨⟨s,hs,hS⟩,⟨t,ht,hT⟩⟩ := kummer_one_roots n hn (.some x y h) H
  rcases he with hx|hx|hx
  · subst x
    rw [actual_first_coordinate n 0 y hn h (by simpa only [zero_add] using mul_ne_zero good_three_ne hn)] at hS
    rw [actual_second_coordinate n 0 y hn h (by simpa using neg_ne_zero.mpr hn)] at hT
    refine ⟨0,t,s,by ring,hT.symm,hS.symm,?_⟩
    rw [hy]
    ring
  · subst x
    rw [actual_first_coordinate n n y hn h (by intro he; apply mul_ne_zero good_four_ne hn; linear_combination he)] at hS
    refine ⟨s/2,0,s,?_,by ring,hS.symm,?_⟩
    · apply (mul_right_cancel₀ good_four_ne)
      have he : (s/2)^2*4=s^2 := by field_simp [good_two_ne]; ring
      rw [he]
      linear_combination -hS
    · rw [hy]; ring
  · subst x
    rw [actual_first_at_root n y hn h] at hS
    rw [actual_second_coordinate n (-3*n) y hn h (by intro he; apply mul_ne_zero good_four_ne hn; linear_combination -he)] at hT
    refine ⟨s*t/(4*n),t,0,?_,hT.symm,by ring,?_⟩
    · calc
        (s*t/(4*n))^2=(s^2*t^2)/(16*n^2) := by field_simp [hn,good_two_ne,good_four_ne,good_sixteen_ne]; ring
        _=(12*n^2)*(-3*n-n)/(16*n^2) := by rw [←hS,←hT]
        _= -3*n := by field_simp [hn,good_two_ne,good_four_ne,good_sixteen_ne]; ring
    · rw [hy]; ring

end ActualTwoDescentFiniteExceptionalHalvingRoots318
