module
public import InfinityValuationDecomposition318
public section
noncomputable section
namespace InfinityValuationFullInertia318
open InfinityReciprocalAction318 InfinityValuationLocal318 InfinityValuationDecomposition318 IsDedekindDomain
open scoped Pointwise
set_option maxHeartbeats 550000
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
local instance valuationLocalization:IsLocalization Q.primeCompl (V c Q hs):=
  InfinityBranchValuation318.actual_localization c Q hs

lemma preserves_of_inertia (e:L c≃ₐ[K]L c)
    (h:restrict c e∈Q.inertia (Order c≃ₐ[Base c]Order c)):
    Q=Q.comap (restrict c e):=by
  ext x
  change x∈Q ↔ restrict c e x∈Q
  have hx:=Ideal.mem_inertia.mp h x
  change restrict c e x-x∈Q at hx
  constructor
  · intro h';simpa only [sub_add_cancel] using Q.add_mem hx h'
  · intro h';simpa only [sub_sub_cancel] using Q.sub_mem h' hx

/-- Both inclusions prove stabilization of the actual embedded valuation
subring, not merely of a source-order prime. -/
@[expose] def ofField (e:L c≃ₐ[K]L c) (he:Q=Q.comap (restrict c e)):D c Q hs:=by
  refine ⟨e,?_⟩
  change e • V c Q hs=V c Q hs
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hh:=ambient_square c Q hs e he (⟨y,hy⟩:V c Q hs)
    change ((localEquiv c Q hs e he ⟨y,hy⟩:V c Q hs):L c)=e y at hh
    change e y∈V c Q hs
    rw [←hh]
    exact (localEquiv c Q hs e he ⟨y,hy⟩).property
  · intro hx
    let y:V c Q hs:=(localEquiv c Q hs e he).symm ⟨x,hx⟩
    refine ⟨y.val,y.property,?_⟩
    have hh:=ambient_square c Q hs e he y
    change ((localEquiv c Q hs e he y:V c Q hs):L c)=e y.val at hh
    change e y.val=x
    rw [←hh]
    simp only [y,RingEquiv.apply_symm_apply]

include hs in
lemma diagonal_in_order_inertia (b:Bool):
    restrict c (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (fun _=>b))∈
      Q.inertia (Order c≃ₐ[Base c]Order c):=by
  change InfinitySignCoordinates318.sign c (fun _=>b)∈Q.inertia (Order c≃ₐ[Base c]Order c)
  apply (InfinityPrimeSignInertia318.sign_mem_exactly c Q hs _).mpr
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
/-- The exact diagonal original field sign, as an actual inertia element. -/
@[expose] def diagonal (b:Bool):(V c Q hs).inertiaSubgroup K:=
  ⟨ofField c Q hs (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (fun _=>b))
      (preserves_of_inertia c Q _ (diagonal_in_order_inertia c Q hs b)),
    (mem_inertia_iff c Q hs _).mpr (diagonal_in_order_inertia c Q hs b)⟩
@[simp] theorem diagonal_field (b:Bool):(diagonal c Q hs b).val.val=
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (fun _=>b):=rfl

theorem diagonal_bijective:Function.Bijective (diagonal c Q hs):=by
  constructor
  · intro b d h
    have hh:=congrArg (fun g:(V c Q hs).inertiaSubgroup K=>g.val.val) h
    have hb: (fun _:Fin 4=>b)=(fun _:Fin 4=>d):=
      FourRootAutomorphisms318.signEquiv_injective (SourceKummerField318.parameter c) hh
    exact congrFun hb 0
  · intro g
    have hg:=(mem_inertia_field_exactly c Q hs g.val).mp g.property
    rcases hg with hg|hg
    · refine ⟨false,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hg.symm
    · refine ⟨true,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hg.symm
/-- Both directions preserve the actual original field automorphism. -/
@[expose] def inertiaEquiv:Bool≃(V c Q hs).inertiaSubgroup K:=
  Equiv.ofBijective (diagonal c Q hs) (diagonal_bijective c Q hs)
theorem inertia_card:Nat.card ((V c Q hs).inertiaSubgroup K)=2:=by
  rw [←Nat.card_congr (inertiaEquiv c Q hs)]
  simp
end InfinityValuationFullInertia318
