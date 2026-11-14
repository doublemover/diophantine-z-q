module
public import PELNormOneNormalizerIntegral318
public section
noncomputable section
namespace PELSquareNormNormalizerKernel318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELActualOrderNormalizer318
open PELQuaternionNormParity318 PELNormOneNormalizerIntegral318
set_option maxHeartbeats 1600000

theorem scalar_conjugation (q : ℚˣ) (x : B) :
    (scalarUnit q:B)*x*(↑(scalarUnit q)⁻¹:B)=x := by
  change algebraMap ℚ B (q:ℚ)*x*algebraMap ℚ B (↑q⁻¹:ℚ)=x
  rw [(Algebra.commutes (q:ℚ) x).eq,mul_assoc,←map_mul,Units.val_inv,map_one,mul_one]

theorem scalar_mem (q : ℚˣ) : scalarUnit q∈normalizer := by
  intro x hx
  constructor
  · rw [scalar_conjugation]
    exact hx
  · have h := scalar_conjugation q⁻¹ x
    simpa only [scalarUnit,map_inv,inv_inv] using (show
      (scalarUnit q⁻¹:B)*x*(↑(scalarUnit q⁻¹)⁻¹:B)∈order from h.symm ▸ hx)

/-- The actual square-norm rational-normalizer kernel is scalars times
original norm-one units. No parity-support theorem is smuggled into the
explicit square-norm hypothesis. -/
theorem square_norm_factorization (u : normalizer) (q : ℚˣ)
    (hu : reducedNorm (u.val:B)=(q:ℚ)^2) :
    ∃ v : orderˣ,reducedNorm ((v:order):B)=1 ∧ u.val=scalarUnit q*integralUnit v := by
  let w : normalizer := ⟨scalarUnit q⁻¹*u.val,
    normalizer.mul_mem (scalar_mem q⁻¹) u.property⟩
  have hw : reducedNorm (w.val:B)=1 := by
    change reducedNorm (algebraMap ℚ B (↑q⁻¹:ℚ)*(u.val:B))=1
    rw [norm_mul,norm_scalar,hu]
    change ((q:ℚ)⁻¹)^2*(q:ℚ)^2=1
    field_simp [q.ne_zero]
  refine ⟨integralUnitOfNormOne w hw,integralUnitOfNormOne_norm w hw,?_⟩
  rw [integralUnitOfNormOne_value]
  change u.val=scalarUnit q*(scalarUnit q⁻¹*u.val)
  have hq : scalarUnit q⁻¹=(scalarUnit q)⁻¹ := map_inv (Units.map (algebraMap ℚ B).toMonoidHom) q
  rw [hq,←mul_assoc,mul_inv_cancel,one_mul]

/-- In particular there is no nonintegral norm-one normalizer left over
outside the original integral arithmetic group. -/
theorem norm_one_factorization (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    ∃ v : orderˣ,reducedNorm ((v:order):B)=1 ∧ integralUnit v=u.val :=
  ⟨integralUnitOfNormOne u hu,integralUnitOfNormOne_norm u hu,integralUnitOfNormOne_value u hu⟩
end PELSquareNormNormalizerKernel318
