module
public import SourceValuationInertia318
public import SourceOrderFieldEquiv318
public import Mathlib.RingTheory.Valuation.RamificationGroup
public section
noncomputable section
namespace SourceValuationDecomposition318
open ContactKummerOrder318 Polynomial IsDedekindDomain
open SourceValuationInertia318
open scoped Pointwise
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
local instance sourceDedekind:IsDedekindDomain (SourceOrder c):=SourceBranchValuation318.source_dedekind c
variable {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F) (i:Fin 4)
    (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
local instance kernelPrime:(P c p).IsPrime:=SourceBranchResidueInertia318.prime_isPrime c p
local instance valuationLocalization:IsLocalization (P c p).primeCompl (V c p i ht):=
  SourceBranchValuation318.actual_localization c p i ht
abbrev D:=(V c p i ht).decompositionSubgroup K
/-- The source automorphism corresponding to every actual valuation
stabilizer element, through the specified full-field extension. -/
@[expose] def orderAut (g:D c p i ht):SourceOrder c≃ₐ[R]SourceOrder c:=
  (SourceOrderFieldEquiv318.fieldEquiv c).symm g.val
lemma extend_orderAut (g:D c p i ht):
    SourceOrderAutomorphisms318.extend c (orderAut c p i ht g)=g.val:=
  (SourceOrderFieldEquiv318.fieldEquiv c).apply_symm_apply g.val
@[expose] def action (g:D c p i ht):V c p i ht≃+*V c p i ht:=
  MulSemiringAction.toRingAut (D c p i ht) (V c p i ht) g
lemma action_on_source (g:D c p i ht) (x:SourceOrder c):
    action c p i ht g (algebraMap (SourceOrder c) (V c p i ht) x)=
      algebraMap (SourceOrder c) (V c p i ht) (orderAut c p i ht g x):=by
  apply Subtype.ext
  change g.val (embedding c x)=embedding c (orderAut c p i ht g x)
  rw [←extend_orderAut c p i ht g]
  exact SourceOrderAutomorphisms318.extend_embedding c _ x

lemma orderAut_preserves (g:D c p i ht):P c p=(P c p).comap (orderAut c p i ht g):=by
  ext x
  change x∈P c p ↔ orderAut c p i ht g x∈P c p
  apply not_iff_not.mp
  change x∈(P c p).primeCompl ↔ orderAut c p i ht g x∈(P c p).primeCompl
  rw [←IsLocalization.AtPrime.isUnit_to_map_iff (V c p i ht) (P c p) x,
    ←IsLocalization.AtPrime.isUnit_to_map_iff (V c p i ht) (P c p) (orderAut c p i ht g x),
    ←action_on_source c p i ht g x]
  constructor
  · intro h
    exact h.map (action c p i ht g).toRingHom
  · intro h
    simpa only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,RingEquiv.symm_apply_apply] using h.map (action c p i ht g).symm.toRingHom

/-- The built-in decomposition action and the exact localization action
agree on the whole actual valuation ring. -/
lemma action_eq_local (g:D c p i ht):action c p i ht g=
    localEquiv c p i ht (orderAut c p i ht g) (orderAut_preserves c p i ht g):=by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (P c p).primeCompl
  apply RingHom.ext
  intro x
  exact (action_on_source c p i ht g x).trans
    (localEquiv_on_source c p i ht (orderAut c p i ht g)
      (orderAut_preserves c p i ht g) x).symm

/-- Mathlib's actual valuation inertia subgroup is tested through the
complete residue-field action, not through a renamed order subgroup. -/
theorem mem_inertia_iff (g:D c p i ht):g∈(V c p i ht).inertiaSubgroup K ↔
    orderAut c p i ht g∈(P c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c):=by
  change MulSemiringAction.toRingAut (D c p i ht) (IsLocalRing.ResidueField (V c p i ht)) g=1 ↔ _
  change IsLocalRing.ResidueField.mapEquiv (action c p i ht g)=RingEquiv.refl _ ↔ _
  rw [action_eq_local,residue_identity_iff_inertia]

theorem mem_inertia_exactly (g:D c p i ht):g∈(V c p i ht).inertiaSubgroup K ↔
    orderAut c p i ht g=1∨
      orderAut c p i ht g=SourceSignFieldComparison318.sourceEquiv c (SourceCharacterFields318.flip i):=by
  rw [mem_inertia_iff]
  exact SourceBranchFullInertia318.mem_exactly c p i ht _
end SourceValuationDecomposition318
