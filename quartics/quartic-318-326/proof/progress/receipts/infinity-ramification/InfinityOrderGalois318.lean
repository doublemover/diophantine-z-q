module
public import InfinityReciprocalPrime318
public import BivariateIntegral318
public section
noncomputable section
namespace InfinityOrderGalois318
open InfinityReciprocalAction318
set_option maxHeartbeats 550000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain:IsDomain (Order c):=InfinityOpenChart318.openOrder_domain c
local instance baseDomain:IsDomain (Base c):=
  Localization.Away.isDomain (ReciprocalInfinityBase318.reciprocalDenominator_ne_zero c)
local instance baseDedekind:IsDedekindDomain (Base c):=InfinityReciprocalPrime318.base_dedekind c
local instance orderAlgebra:Algebra (Order c) (L c):=(InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance orderFraction:IsFractionRing (Order c) (L c):=InfinityOpenFractionField318.open_fractionField c
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
abbrev G:=Order c≃ₐ[Base c]Order c
local instance reciprocalAlgebra:Algebra (Base c) (L c):=(ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul:SMul (Base c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule:Module (Base c) (L c):=Algebra.toModule
local instance originalTower:IsScalarTower (Base c) (Order c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=Base c) (S:=Order c) (A:=L c) (fun _=>rfl)
local instance orderClosure:IsIntegralClosure (Order c) (Base c) (L c):=
  ReciprocalInfinityNormalization318.actual_integralClosure c
local instance rawFinite:FiniteDimensional K (L c):=
  Module.finite_of_finrank_pos (by rw [KummerTensorField318.source_raw_degree c];decide)
local instance actualGalois:IsGalois K (L c):=ActualKummerGalois318.source_raw_galois c
/- This generic AKLB consumer keeps the missing reciprocal-base fraction
identification explicit. The final actual application supplies these instances. -/
variable [bk:Algebra (Base c) K] [bf:IsFractionRing (Base c) K]
variable [bt:IsScalarTower (Base c) K (L c)]
include bk bf bt
@[expose] def fieldRestriction:(L c≃ₐ[K]L c)≃*(G c):=
  galRestrict (Base c) K (L c) (Order c)
lemma fieldRestriction_eq (e:L c≃ₐ[K]L c):fieldRestriction c e=restrict c e:=by
  ext x
  apply InfinityOpenFractionField318.openEmbedding_injective c
  exact (algebraMap_galRestrict_apply (Base c) e x).trans (embedding_square c e x).symm

theorem chart_injective:Function.Injective (algebraMap (Base c) (Order c)):=by
  intro x y h
  apply IsFractionRing.injective (Base c) K
  apply RingHom.injective (algebraMap K (L c))
  rw [←IsScalarTower.algebraMap_apply (Base c) K (L c),
    ←IsScalarTower.algebraMap_apply (Base c) K (L c),
    IsScalarTower.algebraMap_apply (Base c) (Order c) (L c),
    IsScalarTower.algebraMap_apply (Base c) (Order c) (L c),h]

theorem finite_flat:Module.Finite (Base c) (Order c)∧Module.Flat (Base c) (Order c):=
  ⟨ReciprocalInfinityBase318.chartMap_finite c,BivariateIntegral318.flat_of_injective (chart_injective c)⟩

theorem group_finite:Finite (G c):=
  Finite.of_surjective (fieldRestriction c) (fieldRestriction c).surjective

theorem invariant:Algebra.IsInvariant (Base c) (Order c) (G c):=
  Algebra.isInvariant_of_isGalois' (Base c) K (L c) (Order c)
theorem galoisGroup:IsGaloisGroup (G c) (Base c) (Order c) where
  faithful:=inferInstance
  commutes:=inferInstance
  isInvariant:=invariant c

/-- The exact reciprocal-order sign is the restriction of its original field sign. -/
@[expose] def signEquiv:(Fin 4→Bool)≃G c:=
  ((SourceOrderAutomorphisms318.signEquiv c).trans
    (SourceOrderFieldEquiv318.fieldEquiv c).toEquiv).trans (fieldRestriction c).toEquiv
lemma signEquiv_apply (b:Fin 4→Bool):signEquiv c b=InfinitySignCoordinates318.sign c b:=by
  change fieldRestriction c (SourceOrderAutomorphisms318.extend c
    (SourceSignFieldComparison318.sourceEquiv c b))=_
  rw [SourceOrderAutomorphisms318.extend_sign,fieldRestriction_eq]
  rfl
end InfinityOrderGalois318
