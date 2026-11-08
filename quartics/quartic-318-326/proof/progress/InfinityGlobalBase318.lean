module
public import SourceNormalChart318
public import ContactGlobalProper318
public import ReciprocalInfinityNormalization318
public section
noncomputable section
namespace InfinityGlobalBase318
open Polynomial CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev R:=ℚ[X]
abbrev A:=ReciprocalInfinityBase318.ReciprocalOpen c
abbrev SourceBase:=ContactKummerOrder318.OpenBase
abbrev Source:=ContactKummerOrder318.OpenOrder c
abbrev L:=InfinityFieldCoordinates318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField

theorem denominator_unit : IsUnit
    (ContactReciprocalBase318.reciprocalPolynomial (ReciprocalInfinityBase318.reciprocalDenominator c)) := by
  rw [ReciprocalInfinityBase318.reciprocalDenominator,map_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro j
  have hq:IsUnit (algebraMap ℚ SourceBase ((c j.succ:ℚ)/(c 0:ℚ))) :=
    (IsUnit.mk0 _ (div_ne_zero (c j.succ).ne_zero (c 0).ne_zero)).map _
  simpa only [ContactReciprocalBase318.reciprocalPolynomial,
    ReciprocalInfinityBase318.linearCoefficient,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
    map_mul,map_sub,map_one,Polynomial.aeval_C,Polynomial.aeval_X,InfinityParameters318.contact] using
      hq.mul (ContactReciprocalBase318.to_reciprocal_factor_unit j.succ)

@[expose] def sourceBaseMap : A c→+*SourceBase :=
  IsLocalization.Away.lift (g:=ContactReciprocalBase318.reciprocalPolynomial)
    (ReciprocalInfinityBase318.reciprocalDenominator c) (denominator_unit c)
@[simp] theorem sourceBaseMap_polynomial (p:R) :
    sourceBaseMap c (algebraMap R (A c) p)=ContactReciprocalBase318.reciprocalPolynomial p :=
  IsLocalization.Away.lift_eq _ _ _

@[expose] def sourceHom : A c→+*Source c:=
  (algebraMap SourceBase (Source c)).comp (sourceBaseMap c)

theorem sourceHom_polynomial (p:R) :
    sourceHom c (algebraMap R (A c) p)=ContactReciprocalCover318.polynomialMap (Source c) p := by
  simp only [sourceHom,RingHom.comp_apply,sourceBaseMap_polynomial,
    ContactReciprocalCover318.polynomialMap,ContactReciprocalCover318.coverHom,
    ContactReciprocalBase318.backward_map]

@[expose] def originalBaseEmbedding : SourceBase→+*L c:=
  (SourceOpenFractionField318.openEmbedding c).comp (algebraMap SourceBase (Source c))

theorem originalBaseEmbedding_t :
    originalBaseEmbedding c (ContactReciprocalBase318.tUnit:SourceBase)=InfinityFieldCoordinates318.t c := by
  rw [ContactReciprocalBase318.tUnit_coe]
  change SourceOpenFractionField318.openEmbedding c
    (algebraMap SourceBase (Source c) (algebraMap R SourceBase X))=_
  rw [SourceOpenFractionField318.openEmbedding_on_polynomial,RatFunc.algebraMap_X]
  rfl

theorem originalBaseEmbedding_inverse :
    originalBaseEmbedding c (↑ContactReciprocalBase318.tUnit⁻¹:SourceBase)=
      (InfinityFieldCoordinates318.t c)⁻¹ := by
  have h:=congrArg (originalBaseEmbedding c) (Units.mul_inv ContactReciprocalBase318.tUnit)
  rw [map_mul,map_one,originalBaseEmbedding_t] at h
  calc
    originalBaseEmbedding c (↑ContactReciprocalBase318.tUnit⁻¹:SourceBase)=
        (InfinityFieldCoordinates318.t c)⁻¹ *
          (InfinityFieldCoordinates318.t c*originalBaseEmbedding c (↑ContactReciprocalBase318.tUnit⁻¹:SourceBase)) := by
      rw [←mul_assoc,inv_mul_cancel₀ (InfinityFieldCoordinates318.t_ne_zero c),one_mul]
    _=(InfinityFieldCoordinates318.t c)⁻¹ := by rw [h,mul_one]

/-- The source and infinity chart base maps agree inside the exact same
original field on the entire localized reciprocal base. -/
theorem embedding_square :
    (SourceOpenFractionField318.openEmbedding c).comp (sourceHom c)=
      ReciprocalInfinityNormalization318.reciprocalEmbedding c := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ReciprocalInfinityBase318.reciprocalDenominator c))
  apply Polynomial.ringHom_ext
  · intro q
    have hC:algebraMap R (A c) (C q)=algebraMap ℚ (A c) q :=
      (IsScalarTower.algebraMap_apply ℚ R (A c) q).symm
    simp only [RingHom.comp_apply,hC,RingHom.map_rat_algebraMap]
  · simp only [RingHom.comp_apply,sourceHom_polynomial,
      ContactReciprocalCover318.polynomial_coordinate,
      ReciprocalInfinityNormalization318.reciprocalEmbedding_coordinate]
    exact originalBaseEmbedding_inverse c

@[expose] def baseOpen : Spec (CommRingCat.of (A c))⟶ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (algebraMap R (A c)))≫JLineAtlas318.chart ℚ 0
instance baseOpen_open : IsOpenImmersion (baseOpen c) := by
  unfold baseOpen A ReciprocalInfinityBase318.ReciprocalOpen
  infer_instance

theorem factorization : ContactProjectiveModel318.coverMap c=
    Spec.map (CommRingCat.ofHom (sourceHom c))≫baseOpen c := by
  have he:(sourceHom c).comp (algebraMap R (A c))=
      ContactReciprocalCover318.polynomialMap (Source c) :=
    RingHom.ext (sourceHom_polynomial c)
  rw [ContactGlobalProper318.reciprocal_factor,←he,CommRingCat.ofHom_comp,Spec.map_comp]
  rfl
end InfinityGlobalBase318
