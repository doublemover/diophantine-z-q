module
public import FourRootActualNormalization318
public import FourRootActualGenericSigns318
public import FourRootProjectivePointComparison318
public section
noncomputable section
namespace FourRootNormalizationDeck318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootCoordinateOverlap318 FourRootActualGenericField318
open FourRootActualNormalization318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (g:FourBinaryCharacters318.Group)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance affineDomain:IsDomain (Affine b):=affine_domain b hb
local instance rawAlgebra:Algebra (Affine b) (L b):=(affineEmbedding b).toAlgebra
local instance rawFraction:IsFractionRing (Affine b) (L b):=
  FourRootActualFractionField318.actual_fractionField b hb
local instance wholeIntegral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance baseQC:QuasiCompact (genericBase b hb):=FourRootActualNormalization318.genericBaseQC b hb
local instance baseQS:QuasiSeparated (genericBase b hb):=FourRootActualNormalization318.genericBaseQS b hb
local instance projectionFinite:IsFinite (FourRootProjectiveProjection318.projection b):=
  FourRootActualProperModel318.projection_finite b

/-- The ORIGINAL full field sign automorphism, in the correct
contravariant Spec direction, not defined by transporting scheme points. -/
@[expose] def specSign:Spec (CommRingCat.of (L b))≅Spec (CommRingCat.of (L b)):=
  Scheme.Spec.mapIso (FourRootActualGenericSigns318.genericAutomorphism b g).toRingEquiv.toCommRingCatIso.op

lemma genericSource_square:(specSign b hb g).hom≫genericSource b hb=
    genericSource b hb≫FourRootSchemeSignAction318.action b g:=by
  have he:(specSign b hb g).hom≫AffineFractionGeneric318.map (Affine b) (L b)=
      AffineFractionGeneric318.map (Affine b) (L b)≫FourRootSchemeSignAction318.finiteMap b g:=by
    change Spec.map (CommRingCat.ofHom
      (FourRootActualGenericSigns318.genericAutomorphism b g).toRingHom)≫
        Spec.map (CommRingCat.ofHom (algebraMap (Affine b) (L b)))=
      Spec.map (CommRingCat.ofHom (algebraMap (Affine b) (L b)))≫
        Spec.map (CommRingCat.ofHom (FourRootCoordinateRingSigns318.finiteEnd b g).toRingHom)
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (FourRootActualGenericSigns318.affineEmbedding_equivariant b g x).symm
  calc
    _=((specSign b hb g).hom≫AffineFractionGeneric318.map (Affine b) (L b))≫finiteChart b:=by
      rw [genericSource,Category.assoc]
    _=(AffineFractionGeneric318.map (Affine b) (L b)≫FourRootSchemeSignAction318.finiteMap b g)≫finiteChart b:=by
      rw [he]
    _=genericSource b hb≫FourRootSchemeSignAction318.action b g:=by
      simp only [genericSource,Category.assoc,FourRootSchemeSignAction318.finite_action]

lemma genericBase_square:(specSign b hb g).hom≫genericBase b hb=genericBase b hb:=by
  unfold genericBase
  rw [←Category.assoc,genericSource_square,Category.assoc,
    FourRootProjectivePointComparison318.deck_over_projective]

/-- Functorial normalization of the ACTUAL original field automorphism.
This is independently built by the normalization universal property, not
by conjugating a permutation of complex points. -/
@[expose] def normalizedSign:(genericBase b hb).normalization≅(genericBase b hb).normalization:=
  NormalizationSourceIso318.iso (genericBase b hb) (genericBase b hb)
    (specSign b hb g) (genericBase_square b hb g)
@[reassoc] lemma normalized_source:
    (genericBase b hb).toNormalization≫(normalizedSign b hb g).hom=
      (specSign b hb g).hom≫(genericBase b hb).toNormalization:=
  NormalizationSourceIso318.iso_source ..
@[reassoc] lemma normalized_base:
    (normalizedSign b hb g).hom≫(genericBase b hb).fromNormalization=
      (genericBase b hb).fromNormalization:=NormalizationSourceIso318.iso_base ..

/-- The normalization Scheme comparison intertwines the original field
inertia action and the independently glued WHOLE algebraic root action.
Equality is the actual universal-property uniqueness, not closed-point
agreement or an assumption of algebraization. -/
theorem comparison_equivariant:
    (comparison b hb).hom≫FourRootSchemeSignAction318.action b g=
      (normalizedSign b hb g).hom≫(comparison b hb).hom:=by
  apply Scheme.Hom.normalization.hom_ext (genericBase b hb) _ _
    (FourRootProjectiveProjection318.projection b)
  · rw [comparison_source_assoc,normalized_source_assoc,comparison_source]
    exact (genericSource_square b hb g).symm
  · rw [Category.assoc,FourRootProjectivePointComparison318.deck_over_projective,comparison_base]
  · rw [Category.assoc,comparison_base,normalized_base]
end FourRootNormalizationDeck318
