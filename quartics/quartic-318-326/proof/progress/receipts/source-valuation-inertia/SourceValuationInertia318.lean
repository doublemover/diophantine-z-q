module
public import SourceBranchValuation318
public import PrimeLocalizationInertia318
public section
noncomputable section
namespace SourceValuationInertia318
open ContactKummerOrder318 Polynomial IsDedekindDomain
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
local instance sourceDedekind:IsDedekindDomain (SourceOrder c):=SourceBranchValuation318.source_dedekind c
variable {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F) (i:Fin 4)
    (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
abbrev P:=SourceBranchResidueInertia318.prime c p
local instance kernelPrime:(P c p).IsPrime:=SourceBranchResidueInertia318.prime_isPrime c p
abbrev V:=SourceBranchValuation318.valuationRing c p i ht
local instance valuationLocalization:IsLocalization (P c p).primeCompl (V c p i ht):=
  SourceBranchValuation318.actual_localization c p i ht
variable (e:SourceOrder c≃ₐ[R]SourceOrder c) (he:P c p=(P c p).comap e)

/-- The automorphism of the actual embedded valuation ring obtained from
the original prime-preserving source-order automorphism. -/
@[expose] def localEquiv:V c p i ht≃+*V c p i ht:=
  PrimeLocalizationInertia318.lift (P c p) (V c p i ht) e.toRingEquiv he
lemma localEquiv_on_source (x:SourceOrder c):
    localEquiv c p i ht e he (algebraMap (SourceOrder c) (V c p i ht) x)=
      algebraMap (SourceOrder c) (V c p i ht) (e x):=
  PrimeLocalizationInertia318.lift_algebraMap (P c p) (V c p i ht) e.toRingEquiv he x

/-- The local automorphism is exactly the restriction of the original
whole-function-field automorphism on every valuation-ring element. -/
theorem ambient_square (x:V c p i ht):
    algebraMap (V c p i ht) (L c) (localEquiv c p i ht e he x)=
      SourceOrderAutomorphisms318.extend c e (algebraMap (V c p i ht) (L c) x):=by
  have hh:(algebraMap (V c p i ht) (L c)).comp (localEquiv c p i ht e he).toRingHom=
      (SourceOrderAutomorphisms318.extend c e).toRingHom.comp
        (algebraMap (V c p i ht) (L c)):=by
    apply IsLocalization.ringHom_ext (P c p).primeCompl
    apply RingHom.ext
    intro y
    change algebraMap (V c p i ht) (L c)
      (localEquiv c p i ht e he (algebraMap (SourceOrder c) (V c p i ht) y))=
      SourceOrderAutomorphisms318.extend c e
        (algebraMap (V c p i ht) (L c) (algebraMap (SourceOrder c) (V c p i ht) y))
    rw [localEquiv_on_source]
    change embedding c (e y)=SourceOrderAutomorphisms318.extend c e (embedding c y)
    exact (SourceOrderAutomorphisms318.extend_embedding c e y).symm
  exact RingHom.congr_fun hh x

/-- Exact identity on the entire residue field of the actual valuation
ring is equivalent to membership in the previously constructed full
source-order inertia group. -/
theorem residue_identity_iff_inertia:
    IsLocalRing.ResidueField.mapEquiv (localEquiv c p i ht e he)=RingEquiv.refl _ ↔
      e∈(P c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c):=by
  rw [localEquiv,PrimeLocalizationInertia318.residue_equiv_identity_iff,Ideal.mem_inertia]
  rfl

/-- Among every prime-preserving original source-order automorphism,
exactly identity and the contact-root flip act trivially on the whole
actual valuation residue field. -/
theorem residue_identity_exactly:
    IsLocalRing.ResidueField.mapEquiv (localEquiv c p i ht e he)=RingEquiv.refl _ ↔
      e=1∨e=SourceSignFieldComparison318.sourceEquiv c (SourceCharacterFields318.flip i):=by
  rw [residue_identity_iff_inertia]
  exact SourceBranchFullInertia318.mem_exactly c p i ht e
end SourceValuationInertia318
