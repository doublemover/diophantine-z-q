module
public import InfinityOrderGalois318
public section
noncomputable section
namespace InfinityOrderInertia318
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
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance reciprocalAlgebra:Algebra (Base c) (L c):=(ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul:SMul (Base c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule:Module (Base c) (L c):=Algebra.toModule
/- The actual reciprocal fraction map is supplied by the final consumer. -/
variable [bk:Algebra (Base c) K] [bf:IsFractionRing (Base c) K]
variable [bt:IsScalarTower (Base c) K (L c)]
include bk bf bt
variable (Q:Ideal (Order c)) [Q.IsPrime]
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
@[expose] def diagonal (b:Bool):Q.inertia (InfinityOrderGalois318.G c):=
  ⟨InfinitySignCoordinates318.sign c (fun _=>b),by
    apply (InfinityPrimeSignInertia318.sign_mem_exactly c Q hs _).mpr
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl⟩
include hs in
theorem diagonal_bijective:Function.Bijective (diagonal c Q hs):=by
  constructor
  · intro b d h
    have hh:=congrArg (fun x:Q.inertia (InfinityOrderGalois318.G c)=>x.val) h
    change InfinitySignCoordinates318.sign c (fun _=>b)=InfinitySignCoordinates318.sign c (fun _=>d) at hh
    rw [←InfinityOrderGalois318.signEquiv_apply,←InfinityOrderGalois318.signEquiv_apply] at hh
    exact congrFun ((InfinityOrderGalois318.signEquiv c).injective hh) 0
  · intro g
    obtain ⟨b,hb⟩:=(InfinityOrderGalois318.signEquiv c).surjective g.val
    rw [InfinityOrderGalois318.signEquiv_apply] at hb
    have hi:=g.property
    rw [←hb] at hi
    rcases (InfinityPrimeSignInertia318.sign_mem_exactly c Q hs b).mp hi with rfl|rfl
    · exact ⟨false,Subtype.ext hb⟩
    · exact ⟨true,Subtype.ext hb⟩
include hs in
theorem ideal_inertia_card:Nat.card (Q.inertia (InfinityOrderGalois318.G c))=2:=by
  rw [←Nat.card_congr (Equiv.ofBijective (diagonal c Q hs) (diagonal_bijective c Q hs))]
  simp
end InfinityOrderInertia318
