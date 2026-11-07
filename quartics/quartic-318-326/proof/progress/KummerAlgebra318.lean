module
public import GeneratorMultiplesTwo318
public section
namespace KummerAlgebra318
open ConcreteG8Domain LocalGenerator318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0

@[expose] def hP : K := pair (-1) (7/4)
@[expose] def jP : K := pair (39/8) (-9/2)

theorem hP_square : hP^2=xP := by
  ext <;> norm_num [hP,xP,pair,pow_succ]

theorem jP_square : jP^2=xP^2-D := by
  ext <;> norm_num [jP,xP,D,i,pair,pow_succ]

theorem hP_jP : hP*jP=yP := by
  ext <;> norm_num [hP,jP,yP,pair]

theorem hP_ne : hP≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [hP,pair] at hh

theorem jP_ne : jP≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [jP,pair] at hh

/-- Exact signed factorization of the literal scalar Kummer row. -/
theorem kummer_factor (h j r : K) (hj : j^2=h^4-D)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    ((h^2-xP)*r-jP*h-hP*j)*((h^2-xP)*r-jP*h+hP*j)=0 := by
  have hpp := hP_square
  have hjp := jP_square
  linear_combination (h^2-xP)*hk - xP*hj - j^2*hpp + h^2*hjp

/-- The two branches are selected without division by h²−xP. -/
theorem kummer_branches (h j r : K) (hj : j^2=h^4-D)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    (h^2-xP)*r=jP*h+hP*j ∨ (h^2-xP)*r=jP*h-hP*j := by
  rcases mul_eq_zero.mp (kummer_factor h j r hj hk) with he | he
  · left; linear_combination he
  · right; linear_combination he

/-- At the coincident-abscissa branch the row gives the doubled abscissa,
so that branch must not be discarded by an inverse assumption. -/
theorem kummer_equal_square (h r : K) (hh : h^2=xP)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    (2*h*jP*r)^2=(xP^2+D)^2 := by
  have he : 2*h*jP*r= -(xP^2+D) := by
    linear_combination -hk + (r^2-xP)*hh
  rw [he]
  ring

end KummerAlgebra318
