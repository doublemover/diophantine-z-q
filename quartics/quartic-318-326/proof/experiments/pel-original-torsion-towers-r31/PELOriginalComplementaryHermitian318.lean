module
public import PELOriginalComplementaryOrder318
public import PELOriginalHermitianForm318
public section
noncomputable section
namespace PELOriginalComplementaryHermitian318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 QuaternionicPeriodAlternating318
open PELPeriodRiemannForm318 PELOriginalHermitianForm318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def linear (a : order) : ComplexVectors →ₗ[ℂ] ComplexVectors :=
  leftLinear (representation a)

/-- The complementary identity is proved on the entire real matrix
space, not merely on rational points or a selected lattice basis. -/
theorem matrix_form (a : order) (M N : RealMatrices) :
    oriented (representation a*M) (representation a*N)+
      oriented (representation (complement a)*M) (representation (complement a)*N)=
      (degree a:ℝ)*oriented M N := by
  rw [matrix_complement,←matrix_weight]
  simp [oriented,pairing,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem inverse_action (a : order) (z : ComplexVectors) :
    (periodEquiv τ hτ).symm (linear a z)=
      representation a*(periodEquiv τ hτ).symm z := by
  apply (periodEquiv τ hτ).injective
  rw [LinearEquiv.apply_symm_apply]
  change linear a z=period τ (representation a*(periodEquiv τ hτ).symm z)
  rw [period_left_mul]
  change linear a z=linear a (periodEquiv τ hτ ((periodEquiv τ hτ).symm z))
  rw [LinearEquiv.apply_symm_apply]

theorem riemann_complement (a : order) (z w : ComplexVectors) :
    riemann τ hτ (linear a z) (linear a w)+
      riemann τ hτ (linear (complement a) z) (linear (complement a) w)=
      (degree a:ℝ)*riemann τ hτ z w := by
  simp only [riemann,inverse_action]
  exact matrix_form a _ _

/-- Exact positive Hermitian identity for every element of the ORIGINAL
order, with the produced nonnegative INTEGER degree. -/
theorem hermitian_complement (a : order) (z w : ComplexVectors) :
    form τ hτ (linear a z) (linear a w)+
      form τ hτ (linear (complement a) z) (linear (complement a) w)=
      (degree a:ℂ)*form τ hτ z w := by
  have h₁ := riemann_complement τ hτ a z (Complex.I • w)
  have h₂ := riemann_complement τ hτ a z w
  simp only [map_smul] at h₁
  have hc₁ := congrArg (fun r:ℝ => (r:ℂ)) h₁
  have hc₂ := congrArg (fun r:ℝ => (r:ℂ)) h₂
  push_cast at hc₁ hc₂
  simp only [form]
  linear_combination hc₁-Complex.I*hc₂
end PELOriginalComplementaryHermitian318
