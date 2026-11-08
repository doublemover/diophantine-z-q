module
public import SourceOpenFractionField318
public import SmoothGenericField318
public section
noncomputable section
namespace SourceNormalChart318
open scoped nonZeroDivisors
open ContactKummerOrder318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

theorem base_integrallyClosed : IsIntegrallyClosed OpenBase := by
  apply isIntegrallyClosed_of_isLocalization OpenBase (Submonoid.powers denominator)
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n denominator_ne_zero)

theorem base_denominator_unit : IsUnit ((algebraMap R K) denominator) :=
  IsUnit.mk0 _ (by simpa only [map_zero] using
    (IsFractionRing.injective R K).ne denominator_ne_zero)
@[expose] def baseFieldMap : OpenBase→+*K:=
  IsLocalization.Away.lift (g:=algebraMap R K) denominator base_denominator_unit
local instance baseFieldAlgebra : Algebra OpenBase K:=baseFieldMap.toAlgebra
local instance baseFieldTower : IsScalarTower R OpenBase K:=
  IsScalarTower.of_algebraMap_eq (by
    intro x
    exact (IsLocalization.Away.lift_eq (S:=OpenBase) (g:=algebraMap R K)
      denominator base_denominator_unit x).symm)
local instance baseFraction : IsFractionRing OpenBase K:=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers denominator) OpenBase K

/-- Normality of the entire original finite-etale contact source, without
an assumed normal component. -/
theorem source_integrallyClosed (c:Fin 4→ℚˣ) : IsIntegrallyClosed (OpenOrder c) := by
  let :=base_integrallyClosed
  let :=ContactKummerOpenDomain318.open_domain c
  let : Module.Finite OpenBase (OpenOrder c):=(open_finite_free_etale c).1
  let : Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2
  exact SmoothGenericField318.smooth_integrallyClosed (R:=OpenBase) (K:=K) (B:=OpenOrder c)
end SourceNormalChart318
