module
public import InfinityOpenFractionField318
public import SmoothGenericField318
public section
noncomputable section
namespace InfinityNormalChart318
open scoped TensorProduct nonZeroDivisors
open InfinityOpenChart318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=InfinityFieldCoordinates318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance openDomain : IsDomain (OpenOrder c):=openOrder_domain c
local instance openFinite : Module.Finite (OpenBase c) (OpenOrder c):=(finite_free_etale_rank_eight c).1
local instance openEtale : Algebra.Etale (OpenBase c) (OpenOrder c):=(finite_free_etale_rank_eight c).2.2.1

theorem base_integrallyClosed : IsIntegrallyClosed (OpenBase c) := by
  apply isIntegrallyClosed_of_isLocalization (OpenBase c) (Submonoid.powers (denominator c))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (denominator_ne_zero c))

@[expose] def baseFieldMap : OpenBase c→+*K:=
  IsLocalization.Away.lift (g:=algebraMap R K) (denominator c)
    (IsUnit.mk0 _ (by simpa only [map_zero] using
      (IsFractionRing.injective R K).ne (denominator_ne_zero c)))
local instance baseFieldAlgebra : Algebra (OpenBase c) K:=(baseFieldMap c).toAlgebra
theorem base_denominator_unit : IsUnit ((algebraMap R K) (denominator c)) :=
  IsUnit.mk0 _ (by simpa only [map_zero] using
    (IsFractionRing.injective R K).ne (denominator_ne_zero c))
local instance baseFieldTower : IsScalarTower R (OpenBase c) K:=
  IsScalarTower.of_algebraMap_eq (by
    intro x
    exact (IsLocalization.Away.lift_eq (S:=OpenBase c) (g:=algebraMap R K) (denominator c) (base_denominator_unit c) x).symm)
local instance baseFraction : IsFractionRing (OpenBase c) K:=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (denominator c)) (OpenBase c) K

/-- Normality of the whole infinity neighborhood is derived from its
actual finite-etale domain presentation; no component is selected. -/
theorem open_integrallyClosed : IsIntegrallyClosed (OpenOrder c) := by
  let :=base_integrallyClosed c
  exact SmoothGenericField318.smooth_integrallyClosed (R:=OpenBase c) (K:=K) (B:=OpenOrder c)

local instance openOriginalAlgebra : Algebra (OpenOrder c) (L c):=
  (InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance originalFraction : IsFractionRing (OpenOrder c) (L c):=
  InfinityOpenFractionField318.open_fractionField c
local instance baseOriginalAlgebra : Algebra (OpenBase c) (L c):=
  ((InfinityOpenFractionField318.openEmbedding c).comp
    (algebraMap (OpenBase c) (OpenOrder c))).toAlgebra
local instance baseOriginalSMul : SMul (OpenBase c) (L c) := (baseOriginalAlgebra c).toSMul
local instance baseOriginalModule : Module (OpenBase c) (L c) := Algebra.toModule
local instance baseOrderSMul : SMul (OpenBase c) (OpenOrder c) :=
  (inferInstance : Algebra (OpenBase c) (OpenOrder c)).toSMul
local instance baseOrderModule : Module (OpenBase c) (OpenOrder c) := Algebra.toModule
local instance baseSelfTower : IsScalarTower (OpenBase c) (OpenBase c) (L c) :=
  IsScalarTower.of_algebraMap_eq (R:=OpenBase c) (S:=OpenBase c) (A:=L c) (fun _=>rfl)
local instance originalTower : IsScalarTower (OpenBase c) (OpenOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=OpenBase c) (S:=OpenOrder c) (A:=L c) (fun _=>rfl)

/-- This exact infinity order is the actual integral closure of its
localized root-coordinate line in the original contact field. -/
theorem actual_integralClosure : IsIntegralClosure (OpenOrder c) (OpenBase c) (L c) := by
  let :=open_integrallyClosed c
  constructor
  · exact InfinityOpenFractionField318.openEmbedding_injective c
  · intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx.tower_top : IsIntegral (OpenOrder c) x)
    · rintro ⟨y,rfl⟩
      exact (IsIntegral.of_finite (OpenBase c) y).map
        (IsScalarTower.toAlgHom (OpenBase c) (OpenOrder c) (L c))
end InfinityNormalChart318
