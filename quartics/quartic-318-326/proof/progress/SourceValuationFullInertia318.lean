module
public import SourceValuationDecomposition318
public section
noncomputable section
namespace SourceValuationFullInertia318
open ContactKummerOrder318 Polynomial IsDedekindDomain
open SourceValuationInertia318 SourceValuationDecomposition318
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

/-- Prime preservation follows from actual full source-order inertia. -/
lemma preserves_of_inertia (e:SourceOrder c≃ₐ[R]SourceOrder c)
    (h:e∈(P c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)):
    P c p=(P c p).comap e:=by
  have hh:=(SourceBranchResidueInertia318.kernel_inertia_iff c p e).mp h
  ext x
  change p x=0 ↔ p (e x)=0
  have hx:=congrArg (fun f:SourceOrder c→ₐ[R]F=>f x) hh
  change p (e x)=p x at hx
  rw [hx]

/-- Every prime-preserving source automorphism gives the actual stabilizer
of the embedded valuation ring, through its exact original field extension. -/
@[expose] def ofOrder (e:SourceOrder c≃ₐ[R]SourceOrder c)
    (he:P c p=(P c p).comap e):D c p i ht:=by
  refine ⟨SourceOrderAutomorphisms318.extend c e,?_⟩
  change SourceOrderAutomorphisms318.extend c e • V c p i ht=V c p i ht
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hs:=ambient_square c p i ht e he (⟨y,hy⟩:V c p i ht)
    change ((localEquiv c p i ht e he ⟨y,hy⟩:V c p i ht):L c)=
      SourceOrderAutomorphisms318.extend c e y at hs
    change SourceOrderAutomorphisms318.extend c e y∈V c p i ht
    rw [←hs]
    exact (localEquiv c p i ht e he ⟨y,hy⟩).property
  · intro hx
    let y:V c p i ht:=(localEquiv c p i ht e he).symm ⟨x,hx⟩
    refine ⟨y.val,y.property,?_⟩
    have hs:=ambient_square c p i ht e he y
    change ((localEquiv c p i ht e he y:V c p i ht):L c)=
      SourceOrderAutomorphisms318.extend c e y.val at hs
    change SourceOrderAutomorphisms318.extend c e y.val=x
    rw [←hs]
    simp only [y,RingEquiv.apply_symm_apply]

lemma orderAut_ofOrder (e:SourceOrder c≃ₐ[R]SourceOrder c)
    (he:P c p=(P c p).comap e):orderAut c p i ht (ofOrder c p i ht e he)=e:=
  (SourceOrderFieldEquiv318.fieldEquiv c).symm_apply_apply e

/-- The actual valuation inertia group, defined by Mathlib on the original
full field, is equivalent to the entire already classified source-order
prime inertia. Both directions retain the exact field extension. -/
@[expose] def inertiaEquiv:
    (V c p i ht).inertiaSubgroup K ≃ (P c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c) where
  toFun g:=⟨orderAut c p i ht g.val,(mem_inertia_iff c p i ht g.val).mp g.property⟩
  invFun e:=⟨ofOrder c p i ht e.val (preserves_of_inertia c p e.val e.property),by
    apply (mem_inertia_iff c p i ht _).mpr
    rw [orderAut_ofOrder]
    exact e.property⟩
  left_inv g:=by
    apply Subtype.ext
    apply Subtype.ext
    exact extend_orderAut c p i ht g.val
  right_inv e:=by
    apply Subtype.ext
    exact orderAut_ofOrder c p i ht e.val (preserves_of_inertia c p e.val e.property)

/-- Actual valuation-theoretic inertia has order two at every finite
contact, for arbitrary rational unit twists and every specified branch prime. -/
theorem inertia_card:Nat.card ((V c p i ht).inertiaSubgroup K)=2:=by
  rw [Nat.card_congr (inertiaEquiv c p i ht)]
  exact SourceBranchFullInertia318.inertia_card c p i ht
/-- The nonidentity inertia element is literally the original field
sign automorphism flipping the contact root and no other root. -/
theorem mem_inertia_field_exactly (g:D c p i ht):g∈(V c p i ht).inertiaSubgroup K ↔
    g.val=1∨g.val=FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
      (SourceCharacterFields318.flip i):=by
  rw [mem_inertia_exactly]
  have h1:orderAut c p i ht g=1 ↔ g.val=1:=by
    constructor
    · intro h
      have hh:=congrArg (SourceOrderFieldEquiv318.fieldEquiv c) h
      rw [SourceOrderFieldEquiv318.fieldEquiv_apply,extend_orderAut,map_one] at hh
      exact hh
    · intro h
      apply (SourceOrderFieldEquiv318.fieldEquiv c).injective
      rw [SourceOrderFieldEquiv318.fieldEquiv_apply,extend_orderAut,map_one,h]
  have hf:orderAut c p i ht g=SourceSignFieldComparison318.sourceEquiv c
      (SourceCharacterFields318.flip i) ↔ g.val=FourRootAutomorphisms318.signEquiv
        (SourceKummerField318.parameter c) (SourceCharacterFields318.flip i):=by
    constructor
    · intro h
      have hh:=congrArg (SourceOrderAutomorphisms318.extend c) h
      rw [extend_orderAut,SourceOrderAutomorphisms318.extend_sign] at hh
      exact hh
    · intro h
      apply (SourceOrderFieldEquiv318.fieldEquiv c).injective
      change SourceOrderAutomorphisms318.extend c (orderAut c p i ht g)=
        SourceOrderAutomorphisms318.extend c (SourceSignFieldComparison318.sourceEquiv c _)
      rw [extend_orderAut,SourceOrderAutomorphisms318.extend_sign,h]
  rw [h1,hf]
end SourceValuationFullInertia318
