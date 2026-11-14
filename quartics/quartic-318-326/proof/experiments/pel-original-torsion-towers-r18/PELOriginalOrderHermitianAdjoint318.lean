module
public import PELOriginalComplementaryAutomorphy318
public section
noncomputable section
namespace PELOriginalOrderHermitianAdjoint318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalComplementaryHermitian318 PELOriginalHermitianForm318
open PELPeriodRiemannForm318 QuaternionicPeriodAlternating318
variable (τ : ℂ) (hτ : 0 < τ.im)
/-- The literal Rosati involution preserves the original half-integral
order. This definition does not assert any represented-dual statement. -/
@[expose] def adjoint (a : order) : order :=
  ⟨PELQuaternionAlgebra318.rosati a,rosati_mem a a.property⟩
lemma matrix_adjoint (a : order) : representation (adjoint a)=(representation a).transpose :=
  rosati_transpose a
lemma riemann_adjoint (a : order) (z w : ComplexVectors) :
    riemann τ hτ (linear a z) w=riemann τ hτ z (linear (adjoint a) w) := by
  simp only [riemann,inverse_action,matrix_adjoint]
  simp [oriented,pairing,Matrix.mul_apply,Fin.sum_univ_two]
  ring
/-- Full original Hermitian adjoint identity on the actual analytic
cover, with the original orientation and complex-linear first slot. -/
lemma hermitian_adjoint (a : order) (z w : ComplexVectors) :
    form τ hτ (linear a z) w=form τ hτ z (linear (adjoint a) w) := by
  have h₁ := riemann_adjoint τ hτ a z (Complex.I • w)
  have h₂ := riemann_adjoint τ hτ a z w
  simp only [map_smul] at h₁
  simp only [form,h₁,h₂]
lemma form_zero_first (w : ComplexVectors) : form τ hτ 0 w=0 :=
  map_zero (PELOriginalHermitianForm318.linear τ hτ w)
lemma form_neg_first (z w : ComplexVectors) : form τ hτ (-z) w= -form τ hτ z w :=
  map_neg (PELOriginalHermitianForm318.linear τ hτ w) z
lemma form_zero_second (z : ComplexVectors) : form τ hτ z 0=0 := by
  rw [hermitian,form_zero_first,map_zero]
lemma form_neg_second (z w : ComplexVectors) : form τ hτ z (-w)= -form τ hτ z w := by
  rw [hermitian,form_neg_first,map_neg,←hermitian]
lemma linear_zero (z : ComplexVectors) : linear (0 : order) z=0 := by
  simp [PELOriginalComplementaryHermitian318.linear,leftLinear]
lemma linear_one (z : ComplexVectors) : linear (1 : order) z=z := by
  simp [PELOriginalComplementaryHermitian318.linear,leftLinear]
lemma linear_neg_one (z : ComplexVectors) : linear (-1 : order) z= -z := by
  simp [PELOriginalComplementaryHermitian318.linear,leftLinear]
end PELOriginalOrderHermitianAdjoint318
