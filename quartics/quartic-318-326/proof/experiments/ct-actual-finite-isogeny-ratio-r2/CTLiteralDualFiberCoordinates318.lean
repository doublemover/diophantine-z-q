module
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

namespace CTLiteralDualFiberCoordinates318

variable {K : Type*} [Field K] [CharZero K]

/-- Reverse 2-isogeny chart, with the normalization X↦X/4, Y↦Y/8. -/
@[expose] def backX (n s : K) : K := (s-4*n+16*n^2/s)/4
@[expose] def backY (n s t : K) : K := (t-16*n^2*t/s^2)/8

/-- Denominators are nonzero for every retained affine preimage. -/
structure Fiber (n x y : K) where
  s : K
  t : K
  s_ne : s≠0
  equation : t^2=s*(s^2-4*n*s+16*n^2)
  image_x : backX n s=x
  image_y : backY n s t=y

@[expose] def liftX (n x y r : K) : K := 2*(x+n+y/r)
@[expose] def liftY (n x y r : K) : K := 2*r*liftX n x y r

theorem affine_roots_product (n x y r : K) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) :
    liftX n x y r * liftX n x y (-r)=16*n^2 := by
  have h : (y/r)^2=(x+n)^2-4*n^2 := by
    rw [div_pow,hr]
    apply (div_eq_iff hx).mpr
    linear_combination he
  simp only [liftX,div_neg]
  linear_combination -(4:K)*h

private theorem affine_roots_sum (n x y r : K) :
    liftX n x y r + liftX n x y (-r)=4*(x+n) := by
  simp only [liftX,div_neg]
  ring

private theorem affine_roots_difference (n x y r : K) :
    liftX n x y r - liftX n x y (-r)=4*(y/r) := by
  simp only [liftX,div_neg]
  ring

private theorem constant_ne (n : K) (hn : n≠0) : (16:K)*n^2≠0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ hn)

/-- Geometry over precisely the chosen scalar r. Includes y=0 with
x≠0: in that case ±r still give opposite nonzero ordinates. -/
def affineFiber (n x y r : K) (hn : n≠0) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) : Fiber n x y := by
  let s := liftX n x y r
  let s' := liftX n x y (-r)
  have hP : s*s'=16*n^2 := affine_roots_product n x y r hx hr he
  have hs : s≠0 := by
    intro hz
    rw [hz,zero_mul] at hP
    exact constant_ne n hn hP.symm
  have hr0 : r≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hr
    exact hx hr.symm
  have hs' : 16*n^2/s=s' := (div_eq_iff hs).2 (by rw [mul_comm s' s,hP])
  have hS : s+s'=4*(x+n) := affine_roots_sum n x y r
  have hD : s-s'=4*(y/r) := affine_roots_difference n x y r
  have hQ : s^2-4*n*s+16*n^2=4*x*s := by
    linear_combination -hP+s*hS
  refine ⟨s,2*r*s,hs,?_,?_,?_⟩
  · rw [hQ]
    linear_combination (4*s^2)*hr
  · unfold backX
    rw [hs']
    apply (div_eq_iff (by norm_num : (4:K)≠0)).2
    linear_combination hS
  · have hTerm : 16*n^2*(2*r*s)/s^2=2*r*s' := by
      apply (div_eq_iff (pow_ne_zero 2 hs)).2
      linear_combination -2*r*s*hP
    unfold backY
    rw [hTerm]
    apply (div_eq_iff (by norm_num : (8:K)≠0)).2
    calc
      2*r*s-2*r*s'=2*r*(s-s') := by ring
      _=y*8 := by rw [hD]; field_simp [hr0] <;> ring

theorem affineFiber_s (n x y r : K) (hn : n≠0) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) : (affineFiber n x y r hn hx hr he).s=liftX n x y r := rfl

theorem affineFiber_t (n x y r : K) (hn : n≠0) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) : (affineFiber n x y r hn hx hr he).t=liftY n x y r := rfl

theorem affine_sign_switch (n x y r : K) (hn : n≠0) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) :
    liftX n x y (-r)=16*n^2/liftX n x y r ∧
      liftY n x y (-r)= -(16*n^2)*liftY n x y r/(liftX n x y r)^2 := by
  have hP := affine_roots_product n x y r hx hr he
  have hs := (affineFiber n x y r hn hx hr he).s_ne
  rw [affineFiber_s] at hs
  have hS : liftX n x y (-r)=16*n^2/liftX n x y r :=
    ((div_eq_iff hs).2 (by rw [mul_comm (liftX n x y (-r)),hP])).symm
  refine ⟨hS,?_⟩
  simp only [liftY,hS]
  field_simp [hs] <;> ring

@[expose] def kernelLiftX (n r : K) : K := 2*(n+r)

theorem kernel_roots_product (n r : K) (hr : r^2= -3*n^2) :
    kernelLiftX n r * kernelLiftX n (-r)=16*n^2 := by
  unfold kernelLiftX
  linear_combination -(4:K)*hr

/-- The exceptional image (0,0) uses the literal root of -3n²,
not the meaningless square root of the zero abscissa. -/
def kernelFiber (n r : K) (hn : n≠0) (hr : r^2= -3*n^2) : Fiber n 0 0 := by
  let s := kernelLiftX n r
  let s' := kernelLiftX n (-r)
  have hP : s*s'=16*n^2 := kernel_roots_product n r hr
  have hs : s≠0 := by
    intro hz
    rw [hz,zero_mul] at hP
    exact constant_ne n hn hP.symm
  have hs' : 16*n^2/s=s' := (div_eq_iff hs).2 (by rw [mul_comm s' s,hP])
  have hS : s+s'=4*n := by dsimp [s,s',kernelLiftX]; ring
  have hQ : s^2-4*n*s+16*n^2=0 := by linear_combination -hP+s*hS
  refine ⟨s,0,hs,?_,?_,?_⟩
  · rw [hQ,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · unfold backX
    rw [hs']
    apply (div_eq_iff (by norm_num : (4:K)≠0)).2
    linear_combination hS
  · simp [backY]

theorem kernelFiber_s (n r : K) (hn : n≠0) (hr : r^2= -3*n^2) :
    (kernelFiber n r hn hr).s=kernelLiftX n r := rfl

theorem kernelFiber_t (n r : K) (hn : n≠0) (hr : r^2= -3*n^2) :
    (kernelFiber n r hn hr).t=0 := rfl

theorem kernel_sign_switch (n r : K) (hn : n≠0) (hr : r^2= -3*n^2) :
    kernelLiftX n (-r)=16*n^2/kernelLiftX n r := by
  have hs := (kernelFiber n r hn hr).s_ne
  rw [kernelFiber_s] at hs
  exact ((div_eq_iff hs).2 (by rw [mul_comm (kernelLiftX n (-r)),kernel_roots_product n r hr])).symm

private theorem fiber_x_poly {n x y : K} (P : Fiber n x y) :
    P.s^2-4*n*P.s+16*n^2=4*x*P.s := by
  have hi : (P.s-4*n+16*n^2/P.s)/4=x := P.image_x
  have h := (div_eq_iff (by norm_num : (4:K)≠0)).1 hi
  calc
    _=P.s*(P.s-4*n+16*n^2/P.s) := by
      field_simp [P.s_ne] <;> ring
    _=_ := by rw [h]; ring

/-- Actual reverse fiber determines exactly the affine root t/(2s). -/
theorem recovered_affine_root {n x y : K} (P : Fiber n x y) :
    (P.t/(2*P.s))^2=x := by
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) P.s_ne))).2
  rw [P.equation,fiber_x_poly P]
  ring

/-- Actual exceptional fiber determines the root s/2−n, with t=0. -/
theorem recovered_kernel_root {n : K} (P : Fiber n 0 0) :
    (P.s/2-n)^2= -3*n^2 ∧ P.t=0 := by
  have h := fiber_x_poly P
  simp only [mul_zero,zero_mul] at h
  constructor
  · apply mul_left_cancel₀ (by norm_num : (4:K)≠0)
    have hEq : (4:K)*(P.s/2-n)^2=P.s^2-4*n*P.s+4*n^2 := by
      have h2 : (2:K)≠0 := by norm_num
      field_simp [h2] <;> ring
    rw [hEq]
    linear_combination h
  · apply (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp
    rw [P.equation,h,mul_zero]

/-- Both chart coordinates recover the original chosen affine fiber.
In particular there is no ambiguity when the original ordinate is zero. -/
theorem affine_coordinate_recovery {n x y : K} (P : Fiber n x y) (hx : x≠0) :
    liftX n x y (P.t/(2*P.s))=P.s ∧ liftY n x y (P.t/(2*P.s))=P.t := by
  let r := P.t/(2*P.s)
  have hr : r^2=x := recovered_affine_root P
  have hr0 : r≠0 := by
    intro h
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hr
    exact hx hr.symm
  have h2 : (2:K)≠0 := by norm_num
  have ht : P.t=2*r*P.s := by
    dsimp [r]
    field_simp [P.s_ne,h2] <;> ring
  have hBackX : (P.s-4*n+16*n^2/P.s)/4=x := P.image_x
  have hX := (div_eq_iff (by norm_num : (4:K)≠0)).1 hBackX
  have hSum : P.s+16*n^2/P.s=4*(x+n) := by linear_combination hX
  have hBackY : (P.t-16*n^2*P.t/P.s^2)/8=y := P.image_y
  have hY := (div_eq_iff (by norm_num : (8:K)≠0)).1 hBackY
  have hT : 16*n^2*P.t/P.s^2=2*r*(16*n^2/P.s) := by
    rw [ht]
    field_simp [P.s_ne] <;> ring
  have hDelta : P.s-16*n^2/P.s=4*(y/r) := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hr0)
    calc
      (2*r)*(P.s-16*n^2/P.s)=y*8 := by
        rw [hT,ht] at hY
        linear_combination hY
      _=(2*r)*(4*(y/r)) := by field_simp [hr0] <;> ring
  have hs : liftX n x y r=P.s := by
    apply mul_left_cancel₀ (by norm_num : (2:K)≠0)
    unfold liftX
    linear_combination -hSum-hDelta
  refine ⟨hs,?_⟩
  unfold liftY
  rw [hs]
  exact ht.symm

/-- Both chart coordinates recover the original exceptional fiber. -/
theorem kernel_coordinate_recovery {n : K} (P : Fiber n 0 0) :
    kernelLiftX n (P.s/2-n)=P.s ∧ P.t=0 := by
  refine ⟨?_,(recovered_kernel_root P).2⟩
  unfold kernelLiftX
  have h2 : (2:K)≠0 := by norm_num
  field_simp [h2] <;> ring

/-- The exact normalized reverse affine outputs lie on the original
cubic, proved without any already-named dual isogeny. -/
theorem back_affine_equation (n s t : K) (hs : s≠0)
    (h : t^2=s*(s^2-4*n*s+16*n^2)) :
    (backY n s t)^2=backX n s*(backX n s-n)*(backX n s+3*n) := by
  let D := 16*n^2
  let U := s-4*n+D/s
  let V := t-D*t/s^2
  have hV : V=t*(s-D/s)/s := by dsimp [V]; field_simp [hs] <;> ring
  have hT : t^2=s^2*U := by
    unfold U D
    rw [h]
    field_simp [hs] <;> ring
  have hA : (s-D/s)^2=(U+4*n)^2-64*n^2 := by
    dsimp [U,D]
    field_simp [hs] <;> ring
  have hM : V^2=U*((U+4*n)^2-64*n^2) := by
    rw [hV,div_pow,mul_pow,hT,hA]
    field_simp [hs] <;> ring
  change (V/8)^2=(U/4)*(U/4-n)*(U/4+3*n)
  rw [div_pow,hM]
  have h4 : (4:K)≠0 := by norm_num
  have h8 : (8:K)≠0 := by norm_num
  field_simp [h4,h8] <;> ring

end CTLiteralDualFiberCoordinates318

#print axioms CTLiteralDualFiberCoordinates318.affineFiber
#print axioms CTLiteralDualFiberCoordinates318.affine_sign_switch
#print axioms CTLiteralDualFiberCoordinates318.affine_coordinate_recovery
#print axioms CTLiteralDualFiberCoordinates318.recovered_kernel_root
