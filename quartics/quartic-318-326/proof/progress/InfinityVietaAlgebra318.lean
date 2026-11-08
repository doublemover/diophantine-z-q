module
public import InfinityChart318
public section
namespace InfinityVietaAlgebra318
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R]

@[expose] def equation (A B u v:R) : R := v-u^3-A*u*v^2-B*v^3
@[expose] def q (A B u₂ v₁ v₂:R) : R := 1-A*u₂*(v₁+v₂)-B*(v₁^2+v₁*v₂+v₂^2)
@[expose] def s (A u₁ u₂ v₁:R) : R := u₁^2+u₁*u₂+u₂^2+A*v₁^2
@[expose] def c (A B a:R) : R := 1+A*a^2+B*a^3
@[expose] def d (A B a b:R) : R := 2*A*a*b+3*B*a^2*b
@[expose] def e (A B a b:R) : R := A*b^2+3*B*a*b^2-a
@[expose] def f (B b:R) : R := B*b^3-b

/-- The divided difference is obtained from the two original equations without cancellation. -/
theorem subtract_equations (A B u₁ v₁ u₂ v₂:R) :
    q A B u₂ v₁ v₂*(v₂-v₁)-s A u₁ u₂ v₁*(u₂-u₁)=
      equation A B u₂ v₂-equation A B u₁ v₁ := by
  simp only [q,s,equation]
  ring

/-- The regular slope retains equal-input and tangent branches. -/
theorem line_relation (A B u₁ v₁ u₂ v₂ a:R)
    (h₁:equation A B u₁ v₁=0) (h₂:equation A B u₂ v₂=0)
    (hq:IsUnit (q A B u₂ v₁ v₂)) (ha:a*q A B u₂ v₁ v₂=s A u₁ u₂ v₁) :
    a*(u₂-u₁)=v₂-v₁ := by
  apply hq.mul_left_cancel
  calc
    _ = s A u₁ u₂ v₁*(u₂-u₁) := by rw [←ha]; ring
    _ = q A B u₂ v₁ v₂*(v₂-v₁) := by
      linear_combination -(subtract_equations A B u₁ v₁ u₂ v₂)+h₁-h₂

/-- Coefficients of the actual cubic after substitution of the regular line. -/
theorem substituted_cubic (A B a b t:R) :
    -equation A B t (a*t+b)=c A B a*t^3+d A B a b*t^2+e A B a b*t+f B b := by
  simp only [equation,c,d,e,f]
  ring

/-- Exact divided-difference identity, also valid on the diagonal. -/
theorem divided_difference (A B u₁ v₁ u₂ v₂ a b:R)
    (hv₁:v₁=a*u₁+b) (hv₂:v₂=a*u₂+b)
    (ha:a*q A B u₂ v₁ v₂=s A u₁ u₂ v₁) :
    c A B a*(u₁^2+u₁*u₂+u₂^2)+d A B a b*(u₁+u₂)+e A B a b=0 := by
  rw [hv₁,hv₂] at ha
  simp only [q,s,c,d,e] at *
  linear_combination -ha

/-- Ring-level Vieta factorization; neither input difference nor a derivative is cancelled. -/
theorem cubic_factor (C D E F u₁ u₂ t:R) :
    C*t^3+D*t^2+E*t+F=
      (C*u₁^3+D*u₁^2+E*u₁+F)+(t-u₁)*
        ((t-u₂)*(C*(t+u₁+u₂)+D)+(C*(u₁^2+u₁*u₂+u₂^2)+D*(u₁+u₂)+E)) := by ring

/-- Reflection of the third intersection satisfies the original infinity equation. -/
theorem output_equation (A B u₁ v₁ u₂ v₂ a b u₃ v₃:R)
    (h₁:equation A B u₁ v₁=0)
    (hv₁:v₁=a*u₁+b) (hv₂:v₂=a*u₂+b)
    (ha:a*q A B u₂ v₁ v₂=s A u₁ u₂ v₁)
    (hu:c A B a*(u₃-u₁-u₂)=d A B a b) (hv₃:v₃=a*u₃-b) :
    equation A B u₃ v₃=0 := by
  have hp : c A B a*u₁^3+d A B a b*u₁^2+e A B a b*u₁+f B b=0 := by
    rw [←substituted_cubic,←hv₁,h₁,neg_zero]
  have hd := divided_difference A B u₁ v₁ u₂ v₂ a b hv₁ hv₂ ha
  have hz : c A B a*(-u₃+u₁+u₂)+d A B a b=0 := by linear_combination -hu
  have hh := cubic_factor (c A B a) (d A B a b) (e A B a b) (f B b) u₁ u₂ (-u₃)
  rw [hp,hd,hz] at hh
  simp only [mul_zero,add_zero] at hh
  rw [←substituted_cubic] at hh
  rw [hv₃]
  simp only [equation] at hh ⊢
  linear_combination hh

end InfinityVietaAlgebra318
