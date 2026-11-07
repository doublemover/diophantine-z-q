module
public import FiniteSquareTest318
public section
namespace PolynomialCandidate318
open ConcreteG8Domain
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Every nonrational root of the stated integer polynomial has one of
the two exact coordinates exhausted by the finite certificate. -/
theorem quadratic_coordinates (a b c:ℤ) (k:ℕ) (u v:ℚ)
    (ha:a≠0) (hv:v≠0)
    (hpoly:(a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0)
    (hdisc:b^2-4*a*c=2*(k:ℤ)^2) :
    u= -(b:ℚ)/(2*(a:ℚ)) ∧ (v=(k:ℚ)/(2*(a:ℚ)) ∨ v= -(k:ℚ)/(2*(a:ℚ))) := by
  have har : (a:ℚ)≠0 := by exact_mod_cast ha
  have hden : 2*(a:ℚ)≠0 := mul_ne_zero (by norm_num) har
  have hr := congrArg QuadraticAlgebra.re hpoly
  have hi := congrArg QuadraticAlgebra.im hpoly
  norm_num [pair,pow_succ] at hr hi
  have hl : 2*(a:ℚ)*u+(b:ℚ)=0 := by
    apply (mul_eq_zero.mp (show v*(2*(a:ℚ)*u+(b:ℚ))=0 by linear_combination hi)).resolve_left hv
  have hd : (b:ℚ)^2-4*(a:ℚ)*(c:ℚ)=2*(k:ℚ)^2 := by exact_mod_cast hdisc
  have hu : u= -(b:ℚ)/(2*(a:ℚ)) := (eq_div_iff hden).mpr (by linear_combination hl)
  have hs : (2*(a:ℚ)*v)^2=(k:ℚ)^2 := by
    linear_combination 2*(a:ℚ)*hr - ((a:ℚ)*u+(b:ℚ)/2)*hl + hd/2
  refine ⟨hu,?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with hp|hm
  · left; exact (eq_div_iff hden).mpr (by simpa [mul_comm] using hp)
  · right; exact (eq_div_iff hden).mpr (by simpa [mul_comm] using hm)

/-- The integer discriminant equation reconstructs exactly the quotient,
remainder, and primitive gcd checks used by the executable candidate test. -/
theorem primitive_candidate (a:ℕ) (b c:ℤ) (k:ℕ) (ha:0<a)
    (hc:c.natAbs≤81) (hg:Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1)
    (hd:b^2-4*(a:ℤ)*c=2*(k:ℤ)^2) :
    FiniteSquareTest318.PrimitiveCandidate a b k := by
  have ha0 : (4*(a:ℤ))≠0 := by omega
  have he : b^2-2*(k:ℤ)^2=4*(a:ℤ)*c := by linarith
  unfold FiniteSquareTest318.PrimitiveCandidate
  rw [he]
  have hdv : (4*(a:ℤ)*c)/(4*(a:ℤ))=c := by exact Int.mul_ediv_cancel_left c ha0
  simp only [hdv]
  exact ⟨Int.emod_eq_zero_of_dvd ⟨c,rfl⟩,hc,hg⟩

end PolynomialCandidate318
