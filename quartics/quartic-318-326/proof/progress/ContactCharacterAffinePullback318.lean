module
public import ContactCharacterDifferentials318
public import CharacterCoordinateDifferentials318
public import WeierstrassAffineInvariant318
public import IntrinsicDifferentialSectionPullback318
public section
noncomputable section
namespace ContactCharacterAffinePullback318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def finiteForm (i:Fin 4) :=
  AlgHomDifferential318.map (SourceCharacterAlgebra318.publishedToSource i)
    (WeierstrassAffineInvariant318.form (publishedA i) (publishedB i)
      (ContactCharacterDifferentials318.discriminantUnit i))

/-- Exact full-affine comparison: the algebraic form is the restriction of
the actual globally pulled invariant, through the intrinsic source comparison. -/
theorem finite_restrict (i:Fin 4) :
    IntrinsicChartSections318.sectionMap (SourceGlobalAffine318.chartEmbedding units)
      (ContactIntrinsicDifferentials318.structureMap units)
      (SourceGlobalAffine318.chartEmbedding_over_Q units) (finiteForm i)=
        (ContactIntrinsicDifferentials318.omega units).presheaf.map (homOfLE le_top).op
          (ContactCharacterDifferentials318.differential i) := by
  let f:=CompletedCharacterGlobal318.completedMap i
  let j:=SourceGlobalAffine318.chartEmbedding units
  let k:=WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)
  let p:=ContactIntrinsicDifferentials318.structureMap units
  let q:=WeierstrassGluing318.structureMap (publishedA i) (publishedB i)
  have hs:j≫f=Spec.map (CommRingCat.ofHom (SourceCharacterAlgebra318.publishedToSource i).toRingHom)≫k:=
    CompletedCharacterGlobal318.on_finite i
  have hv:=AffineChartPullbackScalars318.image_le f j k _ hs
  have hn:=congrArg (fun m=>m (WeierstrassAffineInvariant318.form (publishedA i) (publishedB i)
    (ContactCharacterDifferentials318.discriminantUnit i)))
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p q
      (CompletedCharacterGlobal318.over_Q i) (SourceCharacterAlgebra318.publishedToSource i) j k
      (SourceGlobalAffine318.chartEmbedding_over_Q units)
      (WeierstrassAffineInvariant318.finite_structure (publishedA i) (publishedB i)) hs hv)
  change IntrinsicDifferentialSectionPullback318.value f p q _ _ _ hv
    (IntrinsicChartSections318.sectionMap k q _
      (WeierstrassAffineInvariant318.form (publishedA i) (publishedB i)
        (ContactCharacterDifferentials318.discriminantUnit i)))=_ at hn
  rw [WeierstrassAffineInvariant318.form_section] at hn
  exact hn.symm.trans (IntrinsicDifferentialSectionPullback318.globalSection_restrict f p q
    (CompletedCharacterGlobal318.over_Q i) _ _ hv (ContactCharacterDifferentials318.invariant i))
end ContactCharacterAffinePullback318
