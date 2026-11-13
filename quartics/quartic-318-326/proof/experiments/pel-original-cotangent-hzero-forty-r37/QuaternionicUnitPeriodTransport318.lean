module
public import QuaternionicMobiusPeriods318
public import QuaternionicOrderPeriodQuotient318
public section
noncomputable section
namespace QuaternionicUnitPeriodTransport318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicOrderPeriodQuotient318
set_option maxHeartbeats 1000000
variable {B : Type*} [Ring B] (ρ : B →+* RealMatrices) (O : Subring B)

@[expose] def unitMatrix (u : Oˣ) : RealMatrices := ρ ((u:O):B)
@[expose] def unitParameter (u : Oˣ) (τ : ℂ) : ℂ := mobius (unitMatrix ρ O u) τ
@[expose] def unitDenominator (u : Oˣ) (τ : ℂ) : ℂ := denominator (unitMatrix ρ O u) τ

theorem unitMatrix_mul_inv (u : Oˣ) : unitMatrix ρ O u*unitMatrix ρ O u⁻¹=1 := by
  change (ρ.comp O.subtype) (u:O)*(ρ.comp O.subtype) (↑u⁻¹:O)=1
  rw [←map_mul,Units.mul_inv,map_one]

theorem unitMatrix_inv_mul (u : Oˣ) : unitMatrix ρ O u⁻¹*unitMatrix ρ O u=1 := by
  change (ρ.comp O.subtype) (↑u⁻¹:O)*(ρ.comp O.subtype) (u:O)=1
  rw [←map_mul,Units.inv_mul,map_one]

/-- Multiplication by the inverse automorphy factor on the actual complex
carrier. The inverse is multiplication by the same denominator. -/
@[expose] def scalarEquiv (d : ℂ) (hd : d≠0) : ComplexVectors ≃ₗ[ℂ] ComplexVectors where
  toFun z := d⁻¹ • z
  invFun z := d • z
  left_inv z := by
    change d • (d⁻¹ • z)=z
    rw [smul_smul,mul_inv_cancel₀ hd,one_smul]
  right_inv z := by
    change d⁻¹ • (d • z)=z
    rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
  map_add' z w := smul_add _ _ _
  map_smul' a z := by
    change d⁻¹ • (a • z)=a • (d⁻¹ • z)
    rw [smul_smul,smul_smul,mul_comm]

variable (u : Oˣ) (τ : ℂ) (hd : unitDenominator ρ O u τ≠0)

theorem period_transport (x : B) :
    periodHom ρ (unitParameter ρ O u τ) x=
      scalarEquiv (unitDenominator ρ O u τ) hd (periodHom ρ τ (x*((u:O):B))) := by
  change period (mobius (unitMatrix ρ O u) τ) (ρ x)=
    (unitDenominator ρ O u τ)⁻¹ • period τ (ρ (x*((u:O):B)))
  rw [map_mul]
  exact period_mobius _ _ τ hd

theorem period_transport_inverse (x : B) :
    scalarEquiv (unitDenominator ρ O u τ) hd (periodHom ρ τ x)=
      periodHom ρ (unitParameter ρ O u τ) (x*((↑u⁻¹:O):B)) := by
  rw [period_transport ρ O u τ hd]
  have hu : ((↑u⁻¹:O):B)*((u:O):B)=1 := congrArg O.subtype (Units.inv_mul u)
  rw [mul_assoc,hu,mul_one]

/-- Equality of the FULL original lattice images. Both inclusions use the
same order unit and its inverse; no rational-span or finite-index shortcut. -/
theorem exact_lattice_transport :
    (periodSubgroup ρ O τ).map
      (scalarEquiv (unitDenominator ρ O u τ) hd).toAddEquiv.toAddMonoidHom=
    periodSubgroup ρ O (unitParameter ρ O u τ) := by
  apply le_antisymm
  · rintro z ⟨w,⟨x,hx,rfl⟩,rfl⟩
    change scalarEquiv (unitDenominator ρ O u τ) hd (periodHom ρ τ x)∈
      periodSubgroup ρ O (unitParameter ρ O u τ)
    rw [period_transport_inverse ρ O u τ hd]
    exact ⟨x*((↑u⁻¹:O):B),O.mul_mem hx (↑u⁻¹:O).property,rfl⟩
  · rintro z ⟨x,hx,rfl⟩
    refine ⟨periodHom ρ τ (x*((u:O):B)),?_,?_⟩
    · exact ⟨x*((u:O):B),O.mul_mem hx (u:O).property,rfl⟩
    · exact (period_transport ρ O u τ hd x).symm

/-- Actual additive equivalence of the two original period quotients. -/
@[expose] def quotientEquiv : PeriodQuotient ρ O τ ≃+
    PeriodQuotient ρ O (unitParameter ρ O u τ) :=
  QuotientAddGroup.congr _ _ (scalarEquiv (unitDenominator ρ O u τ) hd).toAddEquiv
    (exact_lattice_transport ρ O u τ hd)

theorem quotientEquiv_mk (z : ComplexVectors) :
    quotientEquiv ρ O u τ hd (QuotientAddGroup.mk' (periodSubgroup ρ O τ) z)=
      QuotientAddGroup.mk' (periodSubgroup ρ O (unitParameter ρ O u τ))
        (scalarEquiv (unitDenominator ρ O u τ) hd z) := rfl

/-- The change of base commutes with the SAME original left order action. -/
theorem quotientEquiv_order (a : O) (p : PeriodQuotient ρ O τ) :
    quotientEquiv ρ O u τ hd (orderEnd ρ O τ a p)=
      orderEnd ρ O (unitParameter ρ O u τ) a (quotientEquiv ρ O u τ hd p) := by
  refine QuotientAddGroup.induction_on p (fun z => ?_)
  change QuotientAddGroup.mk' _ (scalarEquiv _ hd (leftLinear (ρ a) z))=
    QuotientAddGroup.mk' _ (leftLinear (ρ a) (scalarEquiv _ hd z))
  congr 1
  exact ((leftLinear (ρ a)).map_smul (unitDenominator ρ O u τ)⁻¹ z).symm
end QuaternionicUnitPeriodTransport318
