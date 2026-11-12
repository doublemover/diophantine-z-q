module
public import PELPositiveNormPeriodMap318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace PELIntegralPeriodKernel318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicIntegralPeriodMap318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELComplexPeriodSurface318 PELPositiveNormPeriodMap318
set_option maxHeartbeats 1800000
variable (n : order) (hn : 0<reducedNorm (n:B)) (τ : ℂ) (hτ : 0<τ.im)

@[expose] def rightMultiply : order →+ order where
  toFun x := x*n
  map_zero' := zero_mul _
  map_add' x y := add_mul x y _

/-- An original integral order vector x defines a kernel point by dividing
its ACTUAL original period by the exact nonzero denominator scalar. -/
@[expose] def kernelLift : order →+ Surface (translated n τ) where
  toFun x := QuotientAddGroup.mk' (Periods (translated n τ))
    ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
      periodHom representation τ x)
  map_zero' := by
    change QuotientAddGroup.mk' (Periods (translated n τ))
      ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
        periodHom representation τ (0:B))=0
    rw [map_zero,smul_zero,map_zero]
  map_add' x y := by
    change QuotientAddGroup.mk' (Periods (translated n τ))
      ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
        periodHom representation τ ((x:B)+(y:B)))=_
    rw [map_add,smul_add,map_add]

theorem kernelLift_zero (x : order) : originalMap n hn τ hτ (kernelLift n τ x)=0 := by
  rw [show kernelLift n τ x=QuotientAddGroup.mk' (Periods (translated n τ))
    ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
      periodHom representation τ x) from rfl,originalMap_period]
  change QuotientAddGroup.mk' (Periods τ)
    (QuaternionicMobiusPeriods318.denominator (representation n) τ •
      ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
        periodHom representation τ x))=0
  rw [smul_smul,mul_inv_cancel₀ (scalar_nonzero n hn τ hτ),one_smul]
  exact original_order_zero representation order τ x

@[expose] def kernelHom : order →+ (originalMap n hn τ hτ).ker where
  toFun x := ⟨kernelLift n τ x,kernelLift_zero n hn τ hτ x⟩
  map_zero' := Subtype.ext (map_zero (kernelLift n τ))
  map_add' x y := Subtype.ext (map_add (kernelLift n τ) x y)

theorem kernelHom_surjective : Function.Surjective (kernelHom n hn τ hτ) := by
  intro p
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective (Periods (translated n τ)) p.val
  have hzero : QuotientAddGroup.mk' (Periods τ) (periodScalar representation order n τ z)=0 := by
    have h := p.property
    rw [←hz,originalMap_period] at h
    exact h
  obtain ⟨x,hx,he⟩ := (QuotientAddGroup.eq_zero_iff _).mp hzero
  refine ⟨⟨x,hx⟩,?_⟩
  apply Subtype.ext
  change kernelLift n τ ⟨x,hx⟩=p.val
  rw [←hz]
  change QuotientAddGroup.mk' (Periods (translated n τ))
    ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
      periodHom representation τ x)=_
  rw [he]
  change QuotientAddGroup.mk' (Periods (translated n τ))
    ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
      (QuaternionicMobiusPeriods318.denominator (representation n) τ • z))=_
  rw [smul_smul,inv_mul_cancel₀ (scalar_nonzero n hn τ hτ),one_smul]

/-- The entire kernel of the integral parameterization is exactly the
right lattice O*n, not merely contained in it or equal after tensoring with Q. -/
theorem kernel_eq_right_range : (kernelHom n hn τ hτ).ker=(rightMultiply n).range := by
  ext x
  constructor
  · intro hx
    have hx0 : kernelLift n τ x=0 := congrArg Subtype.val hx
    obtain ⟨y,hy,he⟩ := (QuotientAddGroup.eq_zero_iff _).mp hx0
    have hperiod : periodHom representation τ (y*n)=periodHom representation τ x := by
      rw [←scalar_period representation order n τ (scalar_nonzero n hn τ hτ) y,he]
      change QuaternionicMobiusPeriods318.denominator (representation n) τ •
        ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
          periodHom representation τ x)=_
      rw [smul_smul,mul_inv_cancel₀ (scalar_nonzero n hn τ hτ),one_smul]
    refine ⟨⟨y,hy⟩,?_⟩
    apply Subtype.ext
    apply representation_injective
    apply (periodEquiv τ hτ).injective
    exact hperiod
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    change kernelLift n τ (y*n)=0
    change QuotientAddGroup.mk' (Periods (translated n τ))
      ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
        periodHom representation τ ((y:B)*(n:B)))=0
    rw [←scalar_period representation order n τ (scalar_nonzero n hn τ hτ) (y:B)]
    change QuotientAddGroup.mk' (Periods (translated n τ))
      ((QuaternionicMobiusPeriods318.denominator (representation n) τ)⁻¹ •
        (QuaternionicMobiusPeriods318.denominator (representation n) τ •
          periodHom representation (translated n τ) y))=0
    rw [smul_smul,inv_mul_cancel₀ (scalar_nonzero n hn τ hτ),one_smul]
    exact original_order_zero representation order (translated n τ) y

/-- Actual analytic period-map kernel identified with the original
integral right-lattice quotient. This is the exact missing index-to-kernel join. -/
@[expose] def kernelEquiv : (order ⧸ (rightMultiply n).range) ≃+ (originalMap n hn τ hτ).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_right_range n hn τ hτ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (kernelHom n hn τ hτ)
      (kernelHom_surjective n hn τ hτ))
end PELIntegralPeriodKernel318
