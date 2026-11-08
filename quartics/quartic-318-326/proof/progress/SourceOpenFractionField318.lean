module
public import SourceFractionField318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace SourceOpenFractionField318
open scoped TensorProduct
open ContactKummerOrder318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain : IsDomain (SourceOrder c):=source_domain c
local instance orderFree : Module.Free R (SourceOrder c):=(source_finite_free c).2
local instance openDomain : IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
@[expose] def orderToOpen : SourceOrder c→+*OpenOrder c:=
  (openBaseChange c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : SourceOrder c→ₐ[R]OpenBase⊗[R]SourceOrder c).toRingHom
local instance openAlgebra : Algebra (SourceOrder c) (OpenOrder c):=(orderToOpen c).toAlgebra
@[expose] def localizedEquiv : SourceOrder c⊗[R]OpenBase≃ₐ[SourceOrder c]OpenOrder c :=
  { (Algebra.TensorProduct.comm R (SourceOrder c) OpenBase).toRingEquiv.trans
      (openBaseChange c).toRingEquiv with commutes' := by intro x;rfl }
@[expose] def d : SourceOrder c:=algebraMap R (SourceOrder c) denominator

theorem d_ne_zero : d c≠0 := by
  intro h
  have e:=congrArg (embedding c) h
  rw [d,SourceFractionField318.embedding_on_polynomial,map_zero] at e
  have eK:algebraMap R K denominator=0 :=
    (algebraMap K (L c)).injective (by simpa only [map_zero] using e)
  exact denominator_ne_zero ((IsFractionRing.injective R K) (by simpa only [map_zero] using eK))

theorem open_isLocalization : IsLocalization.Away (d c) (OpenOrder c) := by
  letI:IsLocalization.Away (d c) (SourceOrder c⊗[R]OpenBase) := by
    simpa only [d,Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (SourceOrder c)
        (Submonoid.powers denominator)) (SourceOrder c⊗[R]OpenBase))
  exact IsLocalization.isLocalization_of_algEquiv (S:=SourceOrder c⊗[R]OpenBase) _ (localizedEquiv c)
local instance localization : IsLocalization.Away (d c) (OpenOrder c):=open_isLocalization c
local instance originalAlgebra : Algebra (SourceOrder c) (L c):=
  (embedding c).toAlgebra

theorem mapped_d_ne_zero : embedding c (d c)≠0 := by
  simpa only [map_zero] using (embedding_injective c).ne (d_ne_zero c)

/-- The actual localized original four-root order embeds in the original field,
not merely in an abstract isomorphic fraction field. -/
@[expose] def openEmbedding : OpenOrder c→+*L c:=
  IsLocalization.Away.lift (g:=embedding c) (d c)
    (IsUnit.mk0 _ (mapped_d_ne_zero c))
local instance openOriginalAlgebra : Algebra (OpenOrder c) (L c):=(openEmbedding c).toAlgebra
local instance originalTower : IsScalarTower (SourceOrder c) (OpenOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (by
    intro x
    exact (IsLocalization.Away.lift_eq (d c) (IsUnit.mk0 _ (mapped_d_ne_zero c)) x).symm)

theorem open_fractionField : IsFractionRing (OpenOrder c) (L c) := by
  letI:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (d c)) (OpenOrder c) (L c)

theorem openEmbedding_injective : Function.Injective (openEmbedding c) := by
  letI:=open_fractionField c
  exact IsFractionRing.injective (OpenOrder c) (L c)

theorem openEmbedding_on_order (x:SourceOrder c) :
    openEmbedding c (orderToOpen c x)=embedding c x :=
  IsLocalization.Away.lift_eq (d c) (IsUnit.mk0 _ (mapped_d_ne_zero c)) x

theorem orderToOpen_on_polynomial (p:R) :
    orderToOpen c (algebraMap R (SourceOrder c) p)=
      algebraMap OpenBase (OpenOrder c) (algebraMap R OpenBase p) := by
  unfold orderToOpen
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R OpenBase (OpenBase⊗[R]SourceOrder c)]
  exact (openBaseChange c).commutes _

theorem openEmbedding_on_polynomial (p:R) :
    openEmbedding c (algebraMap OpenBase (OpenOrder c) (algebraMap R OpenBase p))=
      algebraMap K (L c) (algebraMap R K p) := by
  rw [←orderToOpen_on_polynomial,openEmbedding_on_order,SourceFractionField318.embedding_on_polynomial]
end SourceOpenFractionField318
