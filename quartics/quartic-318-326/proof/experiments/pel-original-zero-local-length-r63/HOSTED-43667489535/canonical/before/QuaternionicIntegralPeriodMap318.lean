module
public import QuaternionicPositiveDeterminant318
public section
noncomputable section
namespace QuaternionicIntegralPeriodMap318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicMobiusPeriods318
open QuaternionicPositiveDeterminant318
set_option maxHeartbeats 1400000
variable {B : Type*} [Ring B] (ρ : B →+* RealMatrices) (O : Subring B) (n : O)
  (τ : ℂ) (hd : denominator (ρ n) τ≠0)

@[expose] def parameter : ℂ := mobius (ρ n) τ
@[expose] def periodScalar : ComplexVectors →ₗ[ℂ] ComplexVectors where
  toFun z := denominator (ρ n) τ • z
  map_add' z w := smul_add _ _ _
  map_smul' c z := by simp only [smul_smul]; congr 1; ring

include hd in
/-- Multiplication by the actual denominator carries original periods
at the translated parameter to periods of the ACTUAL right lattice O*n. -/
theorem scalar_period (x : B) :
    periodScalar ρ O n τ (periodHom ρ (parameter ρ O n τ) x)=periodHom ρ τ (x*n) := by
  change denominator (ρ n) τ • period (mobius (ρ n) τ) (ρ x)=period τ (ρ (x*n))
  rw [period_mobius _ _ τ hd,map_mul,smul_smul,mul_inv_cancel₀ hd,one_smul]

include hd in
theorem preserves_original_periods :
    periodSubgroup ρ O (parameter ρ O n τ)≤
      (periodSubgroup ρ O τ).comap (periodScalar ρ O n τ).toAddMonoidHom := by
  rintro z ⟨x,hx,rfl⟩
  change periodScalar ρ O n τ (periodHom ρ (parameter ρ O n τ) x)∈periodSubgroup ρ O τ
  rw [scalar_period ρ O n τ hd]
  exact ⟨x*n,O.mul_mem hx n.property,rfl⟩

/-- An actual additive map from the translated original torus to the
original torus. It is generally an isogeny, NOT a lattice equivalence. -/
@[expose] def quotientMap : PeriodQuotient ρ O (parameter ρ O n τ) →+ PeriodQuotient ρ O τ :=
  QuotientAddGroup.map _ _ (periodScalar ρ O n τ).toAddMonoidHom
    (preserves_original_periods ρ O n τ hd)

theorem quotientMap_mk (z : ComplexVectors) :
    quotientMap ρ O n τ hd (QuotientAddGroup.mk' (periodSubgroup ρ O (parameter ρ O n τ)) z)=
      QuotientAddGroup.mk' (periodSubgroup ρ O τ) (periodScalar ρ O n τ z) := rfl

/-- The map is onto because its original complex-linear scalar is nonzero;
no finite-kernel assertion is inferred from this surjectivity alone. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap ρ O n τ hd) := by
  intro p
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (periodSubgroup ρ O τ) p
  refine ⟨QuotientAddGroup.mk' (periodSubgroup ρ O (parameter ρ O n τ))
    ((denominator (ρ n) τ)⁻¹ • z),?_⟩
  rw [quotientMap_mk]
  change QuotientAddGroup.mk' (periodSubgroup ρ O τ)
    (denominator (ρ n) τ • ((denominator (ρ n) τ)⁻¹ • z))=_
  rw [smul_smul,mul_inv_cancel₀ hd,one_smul]

/-- Left multiplication by the original order commutes with this genuine
nonunit map, because the scalar map retains the original complex representation. -/
theorem quotientMap_order (a : O) (p : PeriodQuotient ρ O (parameter ρ O n τ)) :
    quotientMap ρ O n τ hd (orderEnd ρ O (parameter ρ O n τ) a p)=
      orderEnd ρ O τ a (quotientMap ρ O n τ hd p) := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (periodSubgroup ρ O (parameter ρ O n τ)) p
  rw [orderEnd_mk,quotientMap_mk,quotientMap_mk,orderEnd_mk]
  apply congrArg (QuotientAddGroup.mk' (periodSubgroup ρ O τ))
  exact (map_smul (leftLinear (ρ a)) _ _).symm
end QuaternionicIntegralPeriodMap318
