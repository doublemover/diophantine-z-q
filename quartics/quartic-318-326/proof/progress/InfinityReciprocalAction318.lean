module
public import InfinityCharacterUnits318
public import SourceOrderFieldEquiv318
public section
noncomputable section
namespace InfinityReciprocalAction318
open Polynomial
set_option maxHeartbeats 550000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev K:=RatFunc ℚ
abbrev L:=InfinityFieldCoordinates318.L c
abbrev Base:=ReciprocalInfinityBase318.ReciprocalOpen c
abbrev Order:=InfinityOpenChart318.OpenOrder c
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance reciprocalAlgebra:Algebra (Base c) (L c):=(ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul:SMul (Base c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule:Module (Base c) (L c):=Algebra.toModule

/-- Every original K=Q(t)-linear field automorphism fixes the entire actual
reciprocal base, whose coordinate is s=1/t rather than the ramified u. -/
theorem reciprocal_fixed (e:L c≃ₐ[K]L c) (x:Base c):
    e (ReciprocalInfinityNormalization318.reciprocalEmbedding c x)=
      ReciprocalInfinityNormalization318.reciprocalEmbedding c x:=by
  have hh:e.toRingHom.comp (ReciprocalInfinityNormalization318.reciprocalEmbedding c)=
      ReciprocalInfinityNormalization318.reciprocalEmbedding c:=by
    apply IsLocalization.ringHom_ext (Submonoid.powers (ReciprocalInfinityBase318.reciprocalDenominator c))
    apply Polynomial.ringHom_ext
    · intro q
      change e (ReciprocalInfinityNormalization318.reciprocalEmbedding c
        (algebraMap ℚ (Base c) q))=ReciprocalInfinityNormalization318.reciprocalEmbedding c
        (algebraMap ℚ (Base c) q)
      rw [RingHom.map_rat_algebraMap]
      exact RingHom.map_rat_algebraMap e.toRingHom q
    · change e (ReciprocalInfinityNormalization318.reciprocalEmbedding c
        (algebraMap ℚ[X] (Base c) X))=ReciprocalInfinityNormalization318.reciprocalEmbedding c
        (algebraMap ℚ[X] (Base c) X)
      rw [ReciprocalInfinityNormalization318.reciprocalEmbedding_coordinate,map_inv₀]
      exact congrArg Inv.inv (e.commutes RatFunc.X)
  exact RingHom.congr_fun hh x

@[expose] def overReciprocal (e:L c≃ₐ[K]L c):L c≃ₐ[Base c]L c:=
  { e.toRingEquiv with commutes':=reciprocal_fixed c e }

/-- Restriction through the actual whole integral-closure identification. -/
@[expose] def restrict (e:L c≃ₐ[K]L c):Order c≃ₐ[Base c]Order c:=
  (ReciprocalInfinityNormalization318.normalizationEquiv c).trans
    ((overReciprocal c e).mapIntegralClosure.trans
      (ReciprocalInfinityNormalization318.normalizationEquiv c).symm)

/-- The constructed reciprocal-chart automorphism is the restriction of
this exact original full-field automorphism on every chart element. -/
theorem embedding_square (e:L c≃ₐ[K]L c) (x:Order c):
    InfinityOpenFractionField318.openEmbedding c (restrict c e x)=
      e (InfinityOpenFractionField318.openEmbedding c x):=by
  rw [←ReciprocalInfinityNormalization318.normalizationEquiv_embedding]
  change ((ReciprocalInfinityNormalization318.normalizationEquiv c)
    ((ReciprocalInfinityNormalization318.normalizationEquiv c).symm
      ((overReciprocal c e).mapIntegralClosure
        ((ReciprocalInfinityNormalization318.normalizationEquiv c) x))):L c)=_
  rw [AlgEquiv.apply_symm_apply,AlgEquiv.coe_mapIntegralClosure]
  change e ((ReciprocalInfinityNormalization318.normalizationEquiv c x):L c)=_
  rw [ReciprocalInfinityNormalization318.normalizationEquiv_embedding]
end InfinityReciprocalAction318
