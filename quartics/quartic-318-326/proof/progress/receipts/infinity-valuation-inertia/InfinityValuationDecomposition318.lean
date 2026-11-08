module
public import InfinityValuationLocal318
public import Mathlib.RingTheory.Valuation.RamificationGroup
public section
noncomputable section
namespace InfinityValuationDecomposition318
open InfinityReciprocalAction318 InfinityValuationLocal318 IsDedekindDomain
open scoped Pointwise
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
local instance valuationLocalization:IsLocalization Q.primeCompl (V c Q hs):=
  InfinityBranchValuation318.actual_localization c Q hs
abbrev D:=(V c Q hs).decompositionSubgroup K
@[expose] def action (g:D c Q hs):V c Q hs≃+*V c Q hs:=
  MulSemiringAction.toRingAut (D c Q hs) (V c Q hs) g
lemma action_on_order (g:D c Q hs) (x:Order c):
    action c Q hs g (algebraMap (Order c) (V c Q hs) x)=
      algebraMap (Order c) (V c Q hs) (restrict c g.val x):=by
  apply Subtype.ext
  change g.val (InfinityOpenFractionField318.openEmbedding c x)=
    InfinityOpenFractionField318.openEmbedding c (restrict c g.val x)
  exact (embedding_square c g.val x).symm
lemma restriction_preserves (g:D c Q hs):Q=Q.comap (restrict c g.val):=by
  ext x
  change x∈Q ↔ restrict c g.val x∈Q
  apply not_iff_not.mp
  change x∈Q.primeCompl ↔ restrict c g.val x∈Q.primeCompl
  rw [←IsLocalization.AtPrime.isUnit_to_map_iff (V c Q hs) Q x,
    ←IsLocalization.AtPrime.isUnit_to_map_iff (V c Q hs) Q (restrict c g.val x),
    ←action_on_order c Q hs g x]
  constructor
  · intro h;exact h.map (action c Q hs g).toRingHom
  · intro h
    simpa only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,RingEquiv.symm_apply_apply] using
      h.map (action c Q hs g).symm.toRingHom
lemma action_eq_local (g:D c Q hs):action c Q hs g=
    localEquiv c Q hs g.val (restriction_preserves c Q hs g):=by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro x
  exact (action_on_order c Q hs g x).trans
    (localEquiv_on_order c Q hs g.val (restriction_preserves c Q hs g) x).symm
/-- Membership in the built-in valuation inertia uses its entire residue field. -/
theorem mem_inertia_iff (g:D c Q hs):g∈(V c Q hs).inertiaSubgroup K ↔
    restrict c g.val∈Q.inertia (Order c≃ₐ[Base c]Order c):=by
  change MulSemiringAction.toRingAut (D c Q hs) (IsLocalRing.ResidueField (V c Q hs)) g=1 ↔ _
  change IsLocalRing.ResidueField.mapEquiv (action c Q hs g)=RingEquiv.refl _ ↔ _
  rw [action_eq_local,residue_identity_iff_inertia]

/-- Every original field automorphism is an actual four-root sign. -/
theorem field_sign_surjective:Function.Surjective
    (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)):=by
  intro g
  obtain ⟨e,rfl⟩:=SourceOrderFieldEquiv318.extend_surjective c g
  obtain ⟨b,rfl⟩:=SourceOrderAutomorphisms318.sign_surjective c e
  exact ⟨b,(SourceOrderAutomorphisms318.extend_sign c b).symm⟩
/-- Full valuation inertia is exactly the two diagonal original field signs. -/
theorem mem_inertia_field_exactly (g:D c Q hs):g∈(V c Q hs).inertiaSubgroup K ↔
    g.val=FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (fun _=>false)∨
    g.val=FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (fun _=>true):=by
  obtain ⟨b,hb⟩:=field_sign_surjective c g.val
  rw [mem_inertia_iff,←hb]
  change InfinitySignCoordinates318.sign c b∈Q.inertia (Order c≃ₐ[Base c]Order c) ↔ _
  rw [InfinityPrimeSignInertia318.sign_mem_exactly c Q hs]
  simp only [(FourRootAutomorphisms318.signEquiv_injective (SourceKummerField318.parameter c)).eq_iff]
end InfinityValuationDecomposition318
