module
public import Mathlib.Tactic
public section
namespace LegendreHomogeneousAffine318

/-- A nontrivial homogeneous local solution has an affine norm witness,
even if the supplied solution lies at infinity. The nonzero first coefficient
is essential; zero coefficients belong to the elementary base cases. -/
theorem affine_of_homogeneous {F : Type*} [Field F] [CharZero F]
    (a b x z w : F) (ha : a≠0)
    (hne : ¬(x=0 ∧ z=0 ∧ w=0))
    (hsol : z^2-a*x^2-b*w^2=0) :
    ∃ u v : F, u^2-a*v^2=b := by
  by_cases hw : w=0
  · have hx : x≠0 := by
      intro hx0
      have hz2 : z^2=0 := by simpa [hw,hx0] using hsol
      have hz0 : z=0 :=
        (mul_eq_zero.mp (show z*z=0 by simpa only [pow_two] using hz2)).elim id id
      exact hne ⟨hx0,hz0,hw⟩
    have he : z^2=a*x^2 := by
      apply sub_eq_zero.mp
      simpa only [hw,zero_pow (by decide : 2≠0),mul_zero,sub_zero] using hsol
    let s : F := z/x
    have hs : s^2=a := by
      dsimp [s]
      rw [div_pow,he]
      simp [hx]
    have hs0 : s≠0 := by
      intro hzero
      apply ha
      simpa [hzero] using hs.symm
    refine ⟨(b+1)/2,(b-1)/(2*s),?_⟩
    rw [←hs]
    field_simp [hs0]
    <;> ring
  · refine ⟨z/w,x/w,?_⟩
    calc
      (z/w)^2-a*(x/w)^2=(z^2-a*x^2)/w^2 := by ring
      _=b := by rw [sub_eq_zero.mp hsol]; simp [hw]

end LegendreHomogeneousAffine318
