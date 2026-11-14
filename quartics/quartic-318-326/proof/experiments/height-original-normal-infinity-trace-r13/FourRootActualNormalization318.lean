module
public import FourRootActualProperModel318
public import FourRootActualFractionField318
public import AffineFractionGeneric318
public import NormalizationBirationalComparison318
public section
noncomputable section
namespace FourRootActualNormalization318
open AlgebraicGeometry CategoryTheory Polynomial
open FourRootGluedScheme318 FourRootCoordinateOverlap318 FourRootActualGenericField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
abbrev L:=KummerTensorField318.Raw (parameter b)
local instance affineDomain:IsDomain (Affine b):=affine_domain b hb
local instance rawAlgebra:Algebra (Affine b) (L b):=(affineEmbedding b).toAlgebra
local instance rawFraction:IsFractionRing (Affine b) (L b):=
  FourRootActualFractionField318.actual_fractionField b hb
local instance wholeIntegral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance finiteDominant:IsDominant (finiteChart b):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (finiteChart b).isOpenEmbedding.isOpenMap⟩
local instance projectionFinite:IsFinite (FourRootProjectiveProjection318.projection b):=
  FourRootActualProperModel318.projection_finite b

/-- Actual generic source of the independently glued model, through its
specified entire finite coordinate-ring fraction embedding. -/
@[expose] def genericSource:Spec (CommRingCat.of (L b))⟶scheme b:=
  AffineFractionGeneric318.map (Affine b) (L b)≫finiteChart b
local instance genericDominant:IsDominant (genericSource b hb):=by
  letI:=AffineFractionGeneric318.dominant (Affine b) (L b)
  unfold genericSource
  infer_instance
lemma generic_isIso:IsIso (DominantFunctionField318.map (genericSource b hb)):=by
  letI:=AffineFractionGeneric318.generic_isIso (Affine b) (L b)
  change IsIso (DominantFunctionField318.map
    (AffineFractionGeneric318.map (Affine b) (L b)≫finiteChart b))
  rw [DominantFunctionField318.map_comp,DominantFunctionField318.map_open]
  infer_instance
local instance genericIso:IsIso (DominantFunctionField318.map (genericSource b hb)):=generic_isIso b hb
@[expose] def genericBase:Spec (CommRingCat.of (L b))⟶ProjectiveJLine318.scheme ℂ:=
  genericSource b hb≫FourRootProjectiveProjection318.projection b

/-- The normalization is over EXACTLY the original rational-function t
inside the same degree16 field, not over centered q or a chosen abstract
field isomorphism. -/
lemma genericBase_polynomial:genericBase b hb=
    Spec.map (CommRingCat.ofHom
      ((algebraMap K (L b)).comp (algebraMap (Polynomial ℂ) K)))≫JLineAtlas318.chart ℂ 1:=by
  unfold genericBase genericSource
  rw [Category.assoc,FourRootProjectiveProjection318.finite_projection,←Category.assoc]
  unfold AffineFractionGeneric318.map
  rw [←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact FourRootActualFractionField318.embedding_on_polynomial b p
local instance genericBaseQC:QuasiCompact (genericBase b hb):=
  ⟨fun _ _ _=>(Set.toFinite _).isCompact⟩
local instance genericBaseQS:QuasiSeparated (genericBase b hb):=by
  rw [genericBase_polynomial]
  infer_instance
local instance compositeQC:QuasiCompact
    (genericSource b hb≫FourRootProjectiveProjection318.projection b):=genericBaseQC b hb
local instance compositeQS:QuasiSeparated
    (genericSource b hb≫FourRootProjectiveProjection318.projection b):=genericBaseQS b hb

@[expose] def normalCover:Bool→(scheme b).affineOpens
  | false=>⟨(infinityChart b).opensRange,isAffineOpen_opensRange _⟩
  | true=>⟨(finiteChart b).opensRange,isAffineOpen_opensRange _⟩
lemma normalCover_covers:(⨆k,(normalCover b k).1)=⊤:=by
  apply top_unique
  intro p _
  rcases charts_cover b p with ⟨q,hq⟩|⟨q,hq⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true,q,hq⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false,q,hq⟩
lemma normalCover_sections (k:Bool):IsIntegrallyClosed Γ(scheme b,(normalCover b k).1):=by
  cases k
  · letI:IsIntegrallyClosed (Infinity b):=FourRootInfinitySmooth318.integrallyClosed b hb
    exact IsIntegrallyClosed.of_equiv
      (((Scheme.ΓSpecIso (CommRingCat.of (Infinity b))).symm≪≫
        IsOpenImmersion.ΓIsoTop (infinityChart b)).commRingCatIsoToRingEquiv)
  · letI:IsIntegrallyClosed (Affine b):=FourRootAffineSmooth318.integrallyClosed b hb
    exact IsIntegrallyClosed.of_equiv
      (((Scheme.ΓSpecIso (CommRingCat.of (Affine b))).symm≪≫
        IsOpenImmersion.ΓIsoTop (finiteChart b)).commRingCatIsoToRingEquiv)

/-- The independently constructed whole smooth proper contact Scheme is
isomorphic, as an ACTUAL Scheme over the original projective t-line, to
the genuine relative normalization of its specified full degree16 field.
The isomorphism is constructed by normalization's universal comparison. -/
@[expose] def comparison:(genericBase b hb).normalization≅scheme b:=
  NormalizationBirationalComparison318.iso (genericSource b hb)
    (FourRootProjectiveProjection318.projection b)
    (normalCover b) (normalCover_covers b) (normalCover_sections b hb)
@[reassoc] theorem comparison_source:
    (genericBase b hb).toNormalization≫(comparison b hb).hom=genericSource b hb:=
  NormalizationBirationalComparison318.iso_source ..
@[reassoc] theorem comparison_base:
    (comparison b hb).hom≫FourRootProjectiveProjection318.projection b=
      (genericBase b hb).fromNormalization:=
  NormalizationBirationalComparison318.iso_base ..
end FourRootActualNormalization318
