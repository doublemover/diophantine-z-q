module
public import PeterssonTransition318
public import Mathlib.GroupTheory.GroupAction.Quotient
public section
noncomputable section
open Matrix UpperHalfPlane
namespace DerivativeCocycle318
set_option maxHeartbeats 0
abbrev G := Matrix.GLPos (Fin 2) ℝ

/-- This is the actual complex derivative, expressed by its checked formula. -/
@[expose] def derivative (g:G) (z:UpperHalfPlane) : ℂ :=
  ((g:G):GL (Fin 2) ℝ).val.det / UpperHalfPlane.denom g z ^ 2

theorem derivative_eq (g:G) (z:UpperHalfPlane) : derivative g z=
    deriv (fun w:ℂ=>((g:GL (Fin 2) ℝ) • UpperHalfPlane.ofComplex w:UpperHalfPlane):ℂ→ℂ) z :=
  (UpperHalfPlane.deriv_smul g.property z).symm

theorem derivative_ne_zero (g:G) (z:UpperHalfPlane) : derivative g z≠0 := by
  rw [derivative_eq]
  exact UpperHalfPlane.deriv_smul_ne_zero g.property z

theorem derivative_one (z:UpperHalfPlane) : derivative 1 z=1 := by
  simp [derivative]

/-- Exact chain-rule cocycle with the image point in the first factor. -/
theorem derivative_mul (g h:G) (z:UpperHalfPlane) :
    derivative (g*h) z=derivative g (h • z)*derivative h z := by
  have hs:h • z=(h:Matrix.GeneralLinearGroup (Fin 2) ℝ) • z:=rfl
  rw [hs]
  have hc:=UpperHalfPlane.denom_cocycle (g:GL (Fin 2) ℝ) (h:GL (Fin 2) ℝ) z.im_ne_zero
  rw [←UpperHalfPlane.coe_smul_of_det_pos h.property z] at hc
  simp only [derivative,Subgroup.coe_mul,Units.val_mul,Matrix.det_mul,Complex.ofReal_mul,hc,mul_pow]
  ring

end DerivativeCocycle318
#print axioms DerivativeCocycle318.derivative_mul
