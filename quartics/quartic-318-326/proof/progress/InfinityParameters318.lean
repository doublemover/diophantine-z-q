module
public import QuadraticContactSquareclass318
public import LinearContactSquareclass318
public section
noncomputable section
namespace InfinityParameters318
set_option maxHeartbeats 800000
open Polynomial
variable (c:Fin 4→ℚˣ)
@[expose] def contact (j:Fin 3) : ℚ := LinearContactSquareclass318.contacts j.succ
@[expose] def squaredRoot (j:Fin 3) : ℚ := (c 0:ℚ)/contact j
@[expose] def leading (j:Fin 3) : ℚ := -(c j.succ:ℚ)*contact j/(c 0:ℚ)^2
@[expose] def coefficient (j:Fin 3) : ℚ[X] :=
  C (leading c j)*QuadraticContactSquareclass318.factor (squaredRoot c j)
@[expose] def parameter (j:Fin 3) : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) (coefficient c j)

theorem contact_ne_zero (j:Fin 3) : contact j≠0 := by
  fin_cases j <;> norm_num [contact,LinearContactSquareclass318.contacts]
theorem contact_injective : Function.Injective contact :=
  LinearContactSquareclass318.contacts_injective.comp (Fin.succ_injective 3)

theorem squaredRoot_ne_zero (j:Fin 3) : squaredRoot c j≠0 :=
  div_ne_zero (c 0).ne_zero (contact_ne_zero j)
theorem squaredRoot_injective : Function.Injective (squaredRoot c) := by
  intro i j h
  apply contact_injective
  have hi:=contact_ne_zero i
  have hj:=contact_ne_zero j
  change (c 0:ℚ)/contact i=(c 0:ℚ)/contact j at h
  exact (mul_left_cancel₀ (c 0).ne_zero ((div_eq_div_iff hi hj).mp h)).symm

theorem leading_ne_zero (j:Fin 3) : leading c j≠0 :=
  div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (c j.succ).ne_zero) (contact_ne_zero j))
    (pow_ne_zero _ (c 0).ne_zero)

theorem coefficient_shape (j:Fin 3) : coefficient c j=
    C ((c j.succ:ℚ)/(c 0:ℚ))*(1-C (contact j/(c 0:ℚ))*X^2) := by
  apply Polynomial.funext
  intro x
  simp only [coefficient,leading,QuadraticContactSquareclass318.factor,squaredRoot,
    eval_mul,eval_sub,eval_pow,eval_C,eval_X,eval_one]
  field_simp [(c 0).ne_zero,contact_ne_zero j]
  ring

@[simp] theorem coefficient_at_zero (j:Fin 3) :
    Polynomial.eval 0 (coefficient c j)=(c j.succ:ℚ)/(c 0:ℚ) := by
  rw [coefficient_shape]
  simp

theorem product_nonsquare (s:Finset (Fin 3)) (hs:s.Nonempty) :
    ¬IsSquare (∏j∈s,parameter c j) := by
  have hp:(∏j∈s,parameter c j)=algebraMap ℚ[X] (RatFunc ℚ)
      (C (∏j∈s,leading c j)*∏j∈s,QuadraticContactSquareclass318.factor (squaredRoot c j)) := by
    simp only [parameter,coefficient,←map_prod,Finset.prod_mul_distrib]
  rw [hp]
  exact QuadraticContactSquareclass318.twisted_product_nonsquare _
    (squaredRoot_injective c) (squaredRoot_ne_zero c) s hs _
      (Finset.prod_ne_zero_iff.mpr (fun j _=>leading_ne_zero c j))
end InfinityParameters318
