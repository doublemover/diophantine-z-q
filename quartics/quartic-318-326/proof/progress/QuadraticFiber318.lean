module
public import DerivativeCocycle318
public section
noncomputable section
open DerivativeCocycle318 PeterssonSectionNorm318 PoincareCurvature318
namespace QuadraticFiber318
set_option maxHeartbeats 0

@[ext] structure Fiber where
  point : UpperHalfPlane
  value : ℂ

/-- Induced fiber transport is inverse derivative squared. In contrast,
coordinate pullback multiplies a coefficient by derivative squared. -/
@[expose] def transport (g:G) (v:Fiber) : Fiber :=
  ⟨g • v.point,v.value/(derivative g v.point)^2⟩

instance : SMul G Fiber := ⟨transport⟩

theorem smul_point (g:G) (v:Fiber) : (g • v).point=g • v.point := rfl
theorem smul_value (g:G) (v:Fiber) : (g • v).value=v.value/(derivative g v.point)^2 := rfl

instance : MulAction G Fiber where
  one_smul v := by
    apply Fiber.ext
    · simp only [smul_point,one_smul]
    · simp only [smul_value,derivative_one,one_pow,div_one]
  mul_smul g h v := by
    apply Fiber.ext
    · simp only [smul_point,mul_smul]
    · simp only [smul_value,smul_point,derivative_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
      ring

@[expose] def fiberNorm (v:Fiber) : ℝ := quadraticNorm (coefficient v.point) v.value

theorem fiberNorm_transport (g:G) (v:Fiber) : fiberNorm (g • v)=fiberNorm v := by
  have hh:=PeterssonTransition318.quadratic_transition (g:Matrix.GeneralLinearGroup (Fin 2) ℝ)
    g.property v.point (v.value/(derivative g v.point)^2)
  rw [←derivative_eq,div_mul_cancel₀ _ (pow_ne_zero 2 (derivative_ne_zero g v.point))] at hh
  exact hh.symm

theorem fiberNorm_nonnegative (v:Fiber) : 0≤fiberNorm v := by
  unfold fiberNorm quadraticNorm
  positivity

theorem fiberNorm_eq_zero (v:Fiber) : fiberNorm v=0 ↔ v.value=0 := by
  rw [fiberNorm,quadraticNorm_formula _ (coefficient_positive _)]
  simp only [div_eq_zero_iff,mul_eq_zero,norm_eq_zero]
  have h0:coefficient v.point≠0:=(coefficient_positive v.point).ne'
  simp [h0]

end QuadraticFiber318
#print axioms QuadraticFiber318.fiberNorm_transport
