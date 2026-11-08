module
public import InfinityVietaAlgebra318
public section
namespace BothFiniteLine318
open InfinityVietaAlgebra318
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

@[expose] def thirdX (x t m : R) := m^2-x-t
@[expose] def thirdY (x y t m : R) := m*(x-thirdX x t m)-y

/-- The product of the three ordinates is the norm of the line intercept. -/
lemma ordinate_norm (A B x y t z m : R)
    (hF : y^2-x^3-A*x-B=0)
    (hgap : m*(t-x)-(z-y)=0)
    (htan : m*(y+z)-(x^2+x*t+t^2+A)=0) :
    y*z*thirdY x y t m+(y-m*x)^3+A*m^2*(y-m*x)-B*m^3=0 := by
  unfold thirdY thirdX
  linear_combination m^3*hF+(-m*t*y-2*m*x*y+y^2)*hgap-m^2*y*htan

/-- The companion trace identity uses both divided-difference equations, so it
remains valid on the tangent diagonal over nonreduced coefficient rings. -/
lemma ordinate_trace (A B x y t z m : R)
    (hF : y^2-x^3-A*x-B=0)
    (hgap : m*(t-x)-(z-y)=0)
    (htan : m*(y+z)-(x^2+x*t+t^2+A)=0) :
    (x*z+t*y)*thirdY x y t m+2*A*m*(y-m*x)-3*B*m^2=
      y*z*thirdX x t m := by
  unfold thirdY thirdX
  linear_combination 3*m^2*hF+(-m^2*y-m*t*x-2*m*x^2-t*y)*hgap-
    m*(m*x+2*y)*htan

/-- Compatibility of the two actual Vieta formulas when expressed on the same
line. Only explicit units are cancelled; no input difference is cancelled. -/
theorem coordinates (A B x y t z a b m U V : R)
    (hF : y^2-x^3-A*x-B=0)
    (hgap : m*(t-x)-(z-y)=0)
    (htan : m*(y+z)-(x^2+x*t+t^2+A)=0)
    (hline : a*x+b*y=1) (hslope : a+b*m=0)
    (hy : IsUnit y) (hz : IsUnit z) (hc : IsUnit (c A B a))
    (hU : c A B a*y*z*U=(x*z+t*y)*c A B a+d A B a b*y*z)
    (hV : V=a*U-b) :
    U*thirdY x y t m=thirdX x t m ∧ V*thirdY x y t m=1 := by
  have ha : a= -b*m := by linear_combination hslope
  have hn : b*(y-m*x)=1 := by linear_combination hline-x*hslope
  have hnorm := ordinate_norm A B x y t z m hF hgap htan
  have htrace := ordinate_trace A B x y t z m hF hgap htan
  have hC : c A B a= -b^3*y*z*thirdY x y t m := by
    rw [ha]
    unfold c
    linear_combination b^3*hnorm-
      ((b*(y-m*x))^2+b*(y-m*x)+1+A*b^2*m^2)*hn
  have hD : d A B a b=b^3*(-2*A*m*(y-m*x)+3*B*m^2) := by
    rw [ha]
    unfold d
    linear_combination 2*A*b^2*m*hn
  have hT : ((x*z+t*y)*c A B a+d A B a b*y*z)*thirdY x y t m=
      c A B a*y*z*thirdX x t m := by
    rw [hC,hD]
    linear_combination -b^3*y*z*thirdY x y t m*htrace
  have hout : U*thirdY x y t m=thirdX x t m := by
    apply ((hc.mul hy).mul hz).mul_left_cancel
    calc
      _=(c A B a*y*z*U)*thirdY x y t m := by ring
      _=_ := by rw [hU]; exact hT
  refine ⟨hout,?_⟩
  rw [hV,sub_mul,mul_assoc,hout,ha]
  unfold thirdY thirdX
  linear_combination hn

end BothFiniteLine318
