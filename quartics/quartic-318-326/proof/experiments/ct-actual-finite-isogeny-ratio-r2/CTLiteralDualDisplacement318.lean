module
public import CTLiteralDualTargetAction318
import all CTLiteralDualFiberTargetPoints318
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.Abel
public section

noncomputable section

namespace CTLiteralDualDisplacement318

open CTLiteralDualTargetAction318 CTLiteralDualFiberTargetPoints318
open CTLiteralDualFiberCoordinates318 OriginalSelectedCasselsParity318

variable {F A : Type*} [Field F] [CharZero F] [Field A] [CharZero A]
  [Algebra F A] [DecidableEq A]

local notation "N" => (algebraMap F A)

private theorem action_on_fibres (n : F) (σ : A ≃ₐ[F] A) (hn : N n≠0)
    {x y : A} (P Q : Fiber (N n) x y) (hs : σ P.s=Q.s) (ht : σ P.t=Q.t) :
    targetAction n σ (fiberPoint hn P)=fiberPoint hn Q := by
  unfold fiberPoint
  rw [targetAction_on_point]
  unfold targetPoint
  congr 1
  · exact hs
  · exact ht

private theorem transport_affine (n : F) (σ : A ≃ₐ[F] A) (hn : N n≠0)
    (x y r w : A) (hx : x≠0) (hr : r^2=x) (hw : w^2=x)
    (he : y^2=x*(x-N n)*(x+3*N n))
    (hX : σ x=x) (hY : σ y=y) (hRoot : σ r=w) :
    targetAction n σ (fiberPoint hn (affineFiber (N n) x y r hn hx hr he)) =
      fiberPoint hn (affineFiber (N n) x y w hn hx hw he) := by
  apply action_on_fibres
  · simp only [affineFiber_s,liftX,map_mul,map_add,map_ofNat,map_div₀,σ.commutes,hX,hY,hRoot]
  · simp only [affineFiber_t,liftY,liftX,map_mul,map_add,map_ofNat,map_div₀,σ.commutes,hX,hY,hRoot]

private theorem transport_kernel (n : F) (σ : A ≃ₐ[F] A) (hn : N n≠0)
    (r w : A) (hr : r^2= -3*(N n)^2) (hw : w^2= -3*(N n)^2) (hRoot : σ r=w) :
    targetAction n σ (fiberPoint hn (kernelFiber (N n) r hn hr)) =
      fiberPoint hn (kernelFiber (N n) w hn hw) := by
  apply action_on_fibres
  · simp only [kernelFiber_s,kernelLiftX,map_mul,map_add,map_ofNat,σ.commutes,hRoot]
  · simp only [kernelFiber_t,map_zero]

/-- Literal connecting displacement in the actual E' point group.
Here x,y are the fixed image coordinates, and the sign is on the
same root furnishing the chosen reverse preimage, not a new root. -/
theorem affine_of_root_sign (n : F) (σ : A ≃ₐ[F] A) (hn : N n≠0)
    (x y r : A) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-N n)*(x+3*N n))
    (hX : σ x=x) (hY : σ y=y) (b : Bool)
    (hRoot : σ r=if b then -r else r) :
    let P := fiberPoint hn (affineFiber (N n) x y r hn hx hr he)
    targetAction n σ P - P = if b then targetKernel (N n) hn else 0 := by
  dsimp only
  cases b
  · have h := transport_affine n σ hn x y r r hx hr hr he hX hY (by simpa using hRoot)
    simp [h]
  · have h := transport_affine n σ hn x y r (-r) hx hr (by rw [neg_sq,hr]) he hX hY
        (by simpa using hRoot)
    have hS := affine_switch_is_target_kernel (N n) x y r hn hx hr he
    simp only [if_pos rfl,h,hS] <;> abel

/-- Exceptional (0,0): the root is of -3 n², with the same two
true target-kernel fibres. -/
theorem kernel_of_root_sign (n : F) (σ : A ≃ₐ[F] A) (hn : N n≠0)
    (r : A) (hr : r^2= -3*(N n)^2) (b : Bool)
    (hRoot : σ r=if b then -r else r) :
    let P := fiberPoint hn (kernelFiber (N n) r hn hr)
    targetAction n σ P - P = if b then targetKernel (N n) hn else 0 := by
  dsimp only
  cases b
  · have h := transport_kernel n σ hn r r hr hr (by simpa using hRoot)
    simp [h]
  · have h := transport_kernel n σ hn r (-r) hr (by rw [neg_sq,hr])
        (by simpa using hRoot)
    have hS := kernel_switch_is_target_kernel (N n) r hn hr
    simp only [if_pos rfl,h,hS] <;> abel

theorem origin_displacement (n : F) (σ : A ≃ₐ[F] A) :
    targetAction n σ 0 - 0=0 := by rw [map_zero,sub_zero]

end CTLiteralDualDisplacement318

#print axioms CTLiteralDualDisplacement318.affine_of_root_sign
#print axioms CTLiteralDualDisplacement318.kernel_of_root_sign
