module
public import PolynomialCandidate318
public section
namespace QuadraticDiscriminant318
open ConcreteG8Domain
set_option maxHeartbeats 0

/-- If twice a rational square is integral, the rational number was integral.
The denominator square divides two, hence its denominator equals one. -/
lemma integer_of_twice_square (q : ℚ) (z : ℤ) (h : 2*q^2=(z:ℚ)) :
    ∃ w : ℤ, q=(w:ℚ) := by
  have he : q^2 = Rat.divInt z 2 := by
    rw [Rat.divInt_eq_div]
    linarith
  have hd : (q.den^2:ℤ) ∣ 2 := by
    have := Rat.den_dvd z 2
    rw [←he, Rat.den_pow] at this
    exact_mod_cast this
  have hd' : q.den^2 ∣ 2 := by exact_mod_cast hd
  have hle : q.den^2 ≤ 2 := Nat.le_of_dvd (by decide) hd'
  have hd1 : q.den=1 := by have hp:=q.den_pos; nlinarith
  exact ⟨q.num,(Rat.coe_int_num_of_den_eq_one hd1).symm⟩

/-- The discriminant squareclass is proved from the actual root in Q(sqrt 2),
not assumed as an input to the finite search. -/
lemma actual_root_discriminant (a b c : ℤ) (u v : ℚ) (ha : a ≠ 0) (hv : v ≠ 0)
    (hp : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0) :
    ∃ k : ℕ, 1 ≤ k ∧ b^2-4*a*c=2*(k:ℤ)^2 := by
  have har : (a:ℚ)≠0 := by exact_mod_cast ha
  have hr := congrArg QuadraticAlgebra.re hp
  have hi := congrArg QuadraticAlgebra.im hp
  norm_num [pair,pow_succ] at hr hi
  have hl : 2*(a:ℚ)*u+(b:ℚ)=0 := by
    apply (mul_eq_zero.mp (show v*(2*(a:ℚ)*u+(b:ℚ))=0 by linear_combination hi)).resolve_left hv
  have hd : 2*(2*(a:ℚ)*v)^2 = ((b^2-4*a*c:ℤ):ℚ) := by
    push_cast
    linear_combination 4*(a:ℚ)*hr - (2*(a:ℚ)*u+(b:ℚ))*hl
  obtain ⟨w,hw⟩ := integer_of_twice_square (2*(a:ℚ)*v) (b^2-4*a*c) hd
  have hw0 : w≠0 := by
    intro hz
    rw [hz,Int.cast_zero] at hw
    exact (mul_ne_zero (mul_ne_zero (by norm_num) har) hv) hw
  refine ⟨w.natAbs,by omega,?_⟩
  have he : b^2-4*a*c=2*w^2 := by
    rw [hw] at hd
    exact_mod_cast hd.symm
  simpa only [Int.natCast_natAbs,sq_abs] using he

#print axioms integer_of_twice_square
#print axioms actual_root_discriminant
end QuadraticDiscriminant318
