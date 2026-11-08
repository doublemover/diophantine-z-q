module
public import ThreeTorsionFunctor318
public import ThreeTorsionPoints318
public section
noncomputable section
namespace ThreeTorsionInvolution318
open ThreeTorsionAlgebra318
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def negHom : Ring A B hD→ₐ[R]Ring A B hD :=
  ThreeTorsionFunctor318.toHom A B hD ⟨(x A B hD,-y A B hD),
    ThreeTorsionFunctor318.x_relation A B hD,by
      rw [neg_sq]
      exact equation A B hD⟩
@[simp] theorem negHom_x : negHom A B hD (x A B hD)=x A B hD :=
  ThreeTorsionFunctor318.toHom_x _ _ _ _
@[simp] theorem negHom_y : negHom A B hD (y A B hD)= -y A B hD :=
  ThreeTorsionFunctor318.toHom_y _ _ _ _

theorem negHom_comp : (negHom A B hD).comp (negHom A B hD)=AlgHom.id R (Ring A B hD) := by
  apply ThreeTorsionFunctor318.hom_ext
  · simp
  · simp

/-- The actual coordinate involution (x,y) maps to (x,-y) of the represented family. -/
@[expose] def negEquiv : Ring A B hD≃ₐ[R]Ring A B hD :=
  AlgEquiv.ofAlgHom (negHom A B hD) (negHom A B hD) (negHom_comp A B hD) (negHom_comp A B hD)
@[simp] theorem negEquiv_x : negEquiv A B hD (x A B hD)=x A B hD := negHom_x _ _ _
@[simp] theorem negEquiv_y : negEquiv A B hD (y A B hD)= -y A B hD := negHom_y _ _ _

theorem negEquiv_involutive : Function.Involutive (negEquiv A B hD) := by
  intro b
  exact AlgHom.congr_fun (negHom_comp A B hD) b

end ThreeTorsionInvolution318
