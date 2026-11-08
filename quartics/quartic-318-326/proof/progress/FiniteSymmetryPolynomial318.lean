module
public import InfinityAdditionAlgebra318
public section
namespace FiniteSymmetryPolynomial318
set_option maxHeartbeats 300000
variable {R : Type*} [CommRing R]
@[expose] def X (x t D L:R) := L^2-(x+t)*D^2
@[expose] def Y (x y t D L:R) := L*(x*D^2-X x t D L)-y*D^3
lemma tangent_secant (A B x y t z:R)
    (hF : y^2-x^3-A*x-B=0) (hG : z^2-t^3-A*t-B=0) :
    (x^2+x*t+t^2+A)*(t-x)=(y+z)*(z-y) := by
  linear_combination hF-hG
lemma reversed_X (x t D L:R) : X t x (-D) (-L)=X x t D L := by
  unfold X
  ring
lemma reversed_Y (x y t z D L:R) (h : L*(t-x)=D*(z-y)) :
    Y t z x (-D) (-L)= -Y x y t D L := by
  unfold Y X
  linear_combination -D^2*h
lemma symmetric_X (x t D L:R) : X t x D L=X x t D L := by
  unfold X
  ring
lemma symmetric_Y (x y t z D L:R) (h : L*(t-x)=D*(z-y)) :
    Y t z x D L=Y x y t D L := by
  unfold Y X
  linear_combination D^2*h
end FiniteSymmetryPolynomial318
