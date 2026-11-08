module
public import ContactCharacterAffinePullback318
public import WeierstrassAffineInvariantEquation318
public section
noncomputable section
namespace CharacterPullbackNormalization318
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential
open SourceTwistArithmetic318 CubicInverseCoordinates318 CharacterCoordinateDifferentials318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

lemma cancel_scalar {K M:Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (a b c:K) (ha:IsUnit a) (ω η:M) (h:(a*b) • ω=(a*c) • η) : b • ω=c • η := by
  apply ha.smul_left_cancel.mp
  simpa only [smul_smul] using h

/-- Exact denominator-free pullback identity on the entire original source
coordinate ring. The published coordinate scale occurs with exponent +1. -/
theorem finite_equation (i:Fin 4) :
    (2*z i) • ContactCharacterAffinePullback318.finiteForm i=
      algebraMap ℚ S (CharacterPublishedModels318.scaleUnit i:ℚ) • D ℚ S t := by
  have h:=congrArg (AlgHomDifferential318.map (SourceCharacterAlgebra318.publishedToSource i))
    (WeierstrassAffineInvariantEquation318.equation (publishedA i) (publishedB i)
      (ContactCharacterDifferentials318.discriminantUnit i))
  rw [AlgHomDifferential318.map_smul,CharacterCoordinateDifferentials318.map_dx,
    map_mul,map_ofNat,CubicInverseCoordinates318.source_y] at h
  change (2*(algebraMap ℚ S (yScale i:ℚ)*z i)) •
    ContactCharacterAffinePullback318.finiteForm i=algebraMap ℚ S (xScale i:ℚ) • D ℚ S t at h
  have hs:algebraMap ℚ S (xScale i:ℚ)=
      algebraMap ℚ S (yScale i:ℚ)*algebraMap ℚ S (CharacterPublishedModels318.scaleUnit i:ℚ):=by
    rw [scales,Units.val_mul,map_mul,mul_comm]
  rw [hs,show (2:S)*(algebraMap ℚ S (yScale i:ℚ)*z i)=
    algebraMap ℚ S (yScale i:ℚ)*(2*z i) by ring] at h
  exact cancel_scalar (M:=KaehlerDifferential ℚ S) _ _ _
    ((Units.isUnit (yScale i)).map (algebraMap ℚ S)) _ _ h

@[expose] def scalar (a:S) : Γ(ContactGlobalSmooth318.Model units,
    SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤) :=
  ((SourceGlobalAffine318.chartEmbedding units).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)

@[expose] def restricted (i:Fin 4) : Γ(ContactIntrinsicDifferentials318.omega units,
    SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤) :=
  (ContactIntrinsicDifferentials318.omega units).presheaf.map (homOfLE le_top).op
    (ContactCharacterDifferentials318.differential i)

/-- The same exact identity in the ambient intrinsic Omega on the whole
actual finite chart, for the actual globally pulled differential. -/
theorem intrinsic_finite_equation (i:Fin 4) :
    scalar (2*z i) • restricted i =
      scalar (algebraMap ℚ S (CharacterPublishedModels318.scaleUnit i:ℚ)) •
        (ContactIntrinsicDifferentials318.derivation units).d (scalar t) := by
  have h:=congrArg (IntrinsicChartSections318.sectionMap (SourceGlobalAffine318.chartEmbedding units)
    (ContactIntrinsicDifferentials318.structureMap units)
      (SourceGlobalAffine318.chartEmbedding_over_Q units)) (finite_equation i)
  rw [IntrinsicChartSections318.section_smul,IntrinsicChartSections318.section_smul,
    IntrinsicChartSections318.section_D,ContactCharacterAffinePullback318.finite_restrict] at h
  exact h
end CharacterPullbackNormalization318
