module
public import InfinityFractionField318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace InfinityOpenFractionField318
open scoped TensorProduct
open InfinityOpenChart318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=InfinityFieldCoordinates318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain : IsDomain (Order c):=order_domain c
local instance orderFree : Module.Free R (Order c):=(ThreeRootOrder318.finite_free _).2
local instance openDomain : IsDomain (OpenOrder c):=openOrder_domain c
@[expose] def orderToOpen : Order c→+*OpenOrder c:=
  (openBaseChange c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order c→ₐ[R]OpenBase c⊗[R]Order c).toRingHom
local instance openAlgebra : Algebra (Order c) (OpenOrder c):=(orderToOpen c).toAlgebra
@[expose] def localizedEquiv : Order c⊗[R]OpenBase c≃ₐ[Order c]OpenOrder c :=
  { (Algebra.TensorProduct.comm R (Order c) (OpenBase c)).toRingEquiv.trans
      (openBaseChange c).toRingEquiv with commutes' := by intro x;rfl }
@[expose] def d : Order c:=algebraMap R (Order c) (denominator c)

theorem d_ne_zero : d c≠0 := by
  simpa only [d,map_zero] using (FaithfulSMul.algebraMap_injective R (Order c)).ne
    (denominator_ne_zero c)

theorem open_isLocalization : IsLocalization.Away (d c) (OpenOrder c) := by
  letI:IsLocalization.Away (d c) (Order c⊗[R]OpenBase c) := by
    simpa only [d,Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (Order c)
        (Submonoid.powers (denominator c))) (Order c⊗[R]OpenBase c))
  exact IsLocalization.isLocalization_of_algEquiv (S:=Order c⊗[R]OpenBase c) _ (localizedEquiv c)
local instance localization : IsLocalization.Away (d c) (OpenOrder c):=open_isLocalization c
local instance originalAlgebra : Algebra (Order c) (L c):=
  (InfinityFractionField318.originalEmbedding c).toAlgebra

theorem mapped_d_ne_zero : InfinityFractionField318.originalEmbedding c (d c)≠0 := by
  simpa only [map_zero] using (InfinityFractionField318.originalEmbedding_injective c).ne (d_ne_zero c)

/-- The actual localized infinity order embeds in the original field,
not merely in an abstract isomorphic fraction field. -/
@[expose] def openEmbedding : OpenOrder c→+*L c:=
  IsLocalization.Away.lift (g:=InfinityFractionField318.originalEmbedding c) (d c)
    (IsUnit.mk0 _ (mapped_d_ne_zero c))
local instance openOriginalAlgebra : Algebra (OpenOrder c) (L c):=(openEmbedding c).toAlgebra
local instance originalTower : IsScalarTower (Order c) (OpenOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (by
    intro x
    exact (IsLocalization.Away.lift_eq (d c) (IsUnit.mk0 _ (mapped_d_ne_zero c)) x).symm)

theorem open_fractionField : IsFractionRing (OpenOrder c) (L c) := by
  letI:IsFractionRing (Order c) (L c):=InfinityFractionField318.original_fractionField c
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (d c)) (OpenOrder c) (L c)

theorem openEmbedding_injective : Function.Injective (openEmbedding c) := by
  letI:=open_fractionField c
  exact IsFractionRing.injective (OpenOrder c) (L c)

theorem openEmbedding_on_order (x:Order c) :
    openEmbedding c (orderToOpen c x)=InfinityFractionField318.originalEmbedding c x :=
  IsLocalization.Away.lift_eq (d c) (IsUnit.mk0 _ (mapped_d_ne_zero c)) x
end InfinityOpenFractionField318
