module
public import PELOriginalOrderLatticeMatrix318
public section
noncomputable section
namespace PELOriginalOrderCoverInverse318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalOrderIntegralNorm318
@[expose] def linear (a : order) : ComplexVectors →ₗ[ℂ] ComplexVectors := leftLinear (representation a)
lemma linear_mul (a b : order) (z : ComplexVectors) : linear (a*b) z=linear a (linear b z) := by
  change leftLinear (representation ((a:PELQuaternionAlgebra318.B)*b)) z=_
  rw [map_mul,QuaternionicOrderQuotientActionLaws318.linear_mul]
lemma linear_integer (n : ℤ) (z : ComplexVectors) : linear (n : order) z=(n:ℂ) • z := by
  change leftLinear (representation (n:PELQuaternionAlgebra318.B)) z=_
  rw [map_intCast]
  ext i
  fin_cases i <;> simp [leftLinear,action]
lemma norm_left (a : order) (z : ComplexVectors) :
    linear (conjugate a) (linear a z)=(norm a:ℂ) • z := by
  rw [←linear_mul,conjugate_mul,linear_integer]
lemma norm_right (a : order) (z : ComplexVectors) :
    linear a (linear (conjugate a) z)=(norm a:ℂ) • z := by
  rw [←linear_mul,mul_conjugate,linear_integer]
/-- Actual inverse on the original complex covering space, with the
literal reduced-norm denominator and preserved standard conjugate. -/
@[expose] def equivalence (a : order) (ha : norm a≠0) : ComplexVectors ≃ₗ[ℂ] ComplexVectors :=
  { linear a with
    invFun := fun z => (norm a:ℂ)⁻¹ • linear (conjugate a) z
    left_inv := by
      intro z
      have hn : (norm a:ℂ)≠0 := by exact_mod_cast ha
      rw [norm_left,smul_smul,inv_mul_cancel₀ hn,one_smul]
    right_inv := by
      intro z
      have hn : (norm a:ℂ)≠0 := by exact_mod_cast ha
      rw [map_smul,norm_right,smul_smul,inv_mul_cancel₀ hn,one_smul] }
end PELOriginalOrderCoverInverse318
