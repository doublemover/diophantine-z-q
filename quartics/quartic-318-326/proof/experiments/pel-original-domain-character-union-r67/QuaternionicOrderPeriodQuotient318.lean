module
public import QuaternionicPeriodVariation318
public import Mathlib.GroupTheory.QuotientGroup.Defs
public section
noncomputable section
namespace QuaternionicOrderPeriodQuotient318
open QuaternionicRealPeriod318
set_option maxHeartbeats 800000
variable {B : Type*} [Ring B] (ρ : B →+* RealMatrices) (O : Subring B) (τ : ℂ)

/-- The subgroup is the image of the supplied ORIGINAL order under its
specified splitting and actual periods. No standard Z^4 lattice is substituted. -/
@[expose] def periodHom : B →+ ComplexVectors :=
  (period τ).toAddMonoidHom.comp ρ.toAddMonoidHom
@[expose] def periodSubgroup : AddSubgroup ComplexVectors := O.toAddSubgroup.map (periodHom ρ τ)
abbrev PeriodQuotient := ComplexVectors ⧸ periodSubgroup ρ O τ

@[expose] def leftLinear (g : RealMatrices) : ComplexVectors →ₗ[ℂ] ComplexVectors where
  toFun := action g
  map_add' z w := by funext i; simp only [action,Pi.add_apply]; ring
  map_smul' a z := by
    funext i
    change (g i 0 : ℂ) * (a * z 0) + (g i 1 : ℂ) * (a * z 1) =
      a * ((g i 0 : ℂ) * z 0 + (g i 1 : ℂ) * z 1)
    ring

theorem periodHom_mul (a b : B) : periodHom ρ τ (a*b)=leftLinear (ρ a) (periodHom ρ τ b) := by
  change period τ (ρ (a*b))=action (ρ a) (period τ (ρ b))
  rw [map_mul,period_left_mul]

theorem order_preserves_periods (a : O) :
    periodSubgroup ρ O τ≤(periodSubgroup ρ O τ).comap (leftLinear (ρ a)).toAddMonoidHom := by
  rintro z ⟨b,hb,rfl⟩
  change leftLinear (ρ a) (periodHom ρ τ b)∈periodSubgroup ρ O τ
  rw [←periodHom_mul]
  exact ⟨(a:B)*b,O.mul_mem a.property hb,rfl⟩

/-- The actual order action descends to the quotient by its original periods.
Discreteness, compactness, polarization and algebraization are not assumed or
claimed by this additive-quotient construction. -/
@[expose] def orderEnd (a : O) : PeriodQuotient ρ O τ →+ PeriodQuotient ρ O τ :=
  QuotientAddGroup.map (periodSubgroup ρ O τ) (periodSubgroup ρ O τ)
    (leftLinear (ρ a)).toAddMonoidHom (order_preserves_periods ρ O τ a)

theorem orderEnd_mk (a : O) (z : ComplexVectors) :
    orderEnd ρ O τ a (QuotientAddGroup.mk' (periodSubgroup ρ O τ) z)=
      QuotientAddGroup.mk' (periodSubgroup ρ O τ) (leftLinear (ρ a) z) := rfl

/-- Every element of the specified order really is killed by the quotient
period map, with no weakening to its rational or real span. -/
theorem original_order_zero (a : O) :
    QuotientAddGroup.mk' (periodSubgroup ρ O τ) (periodHom ρ τ a)=0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨(a:B),a.property,rfl⟩

/-- The same representation preserves the transported complex structure;
this records the holomorphic linear action before passage to any lattice. -/
theorem action_complex_structure (hτ : 0<τ.im) (a : B) (M : RealMatrices) :
    complexStructure τ hτ (ρ a*M)=ρ a*complexStructure τ hτ M :=
  complexStructure_commutes τ hτ (ρ a) M
end QuaternionicOrderPeriodQuotient318
