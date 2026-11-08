module
public import InfinityBranchValuation318
public import PrimeLocalizationInertia318
public section
noncomputable section
namespace InfinityValuationLocal318
open InfinityReciprocalAction318 IsDedekindDomain
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance orderDomain:IsDomain (Order c):=InfinityOpenChart318.openOrder_domain c
local instance orderAlgebra:Algebra (Order c) (L c):=(InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance orderFraction:IsFractionRing (Order c) (L c):=InfinityOpenFractionField318.open_fractionField c
local instance orderDedekind:IsDedekindDomain (Order c):=InfinityBranchValuation318.order_dedekind c
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
variable (Q:Ideal (Order c)) [Q.IsPrime]
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
abbrev V:=InfinityBranchValuation318.valuationRing c Q hs
local instance valuationLocalization:IsLocalization Q.primeCompl (V c Q hs):=
  InfinityBranchValuation318.actual_localization c Q hs
variable (e:L c≃ₐ[K]L c) (he:Q=Q.comap (restrict c e))
@[expose] def localEquiv:V c Q hs≃+*V c Q hs:=
  PrimeLocalizationInertia318.lift Q (V c Q hs) (restrict c e).toRingEquiv he
lemma localEquiv_on_order (x:Order c):
    localEquiv c Q hs e he (algebraMap (Order c) (V c Q hs) x)=
      algebraMap (Order c) (V c Q hs) (restrict c e x):=
  PrimeLocalizationInertia318.lift_algebraMap Q (V c Q hs) (restrict c e).toRingEquiv he x
/-- Entire localized ring compatibility in the original specified field. -/
theorem ambient_square (x:V c Q hs):
    algebraMap (V c Q hs) (L c) (localEquiv c Q hs e he x)=
      e (algebraMap (V c Q hs) (L c) x):=by
  have hh:(algebraMap (V c Q hs) (L c)).comp (localEquiv c Q hs e he).toRingHom=
      e.toRingHom.comp (algebraMap (V c Q hs) (L c)):=by
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro y
    change algebraMap (V c Q hs) (L c)
      (localEquiv c Q hs e he (algebraMap (Order c) (V c Q hs) y))=
      e (algebraMap (V c Q hs) (L c) (algebraMap (Order c) (V c Q hs) y))
    rw [localEquiv_on_order]
    exact embedding_square c e y
  exact RingHom.congr_fun hh x
/-- The whole actual local residue-field action, not only the generators. -/
theorem residue_identity_iff_inertia:
    IsLocalRing.ResidueField.mapEquiv (localEquiv c Q hs e he)=RingEquiv.refl _ ↔
      restrict c e∈Q.inertia (Order c≃ₐ[Base c]Order c):=by
  rw [localEquiv,PrimeLocalizationInertia318.residue_equiv_identity_iff,Ideal.mem_inertia]
  rfl
end InfinityValuationLocal318
