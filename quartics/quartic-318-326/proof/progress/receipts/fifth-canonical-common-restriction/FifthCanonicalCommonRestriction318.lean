module
public import FifthActualDifferentialRestriction318
public section
noncomputable section
namespace FifthCanonicalCommonRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthActualDifferential318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev X:=ContactGlobalSmooth318.Model units
abbrev O:=ContactKummerOrder318.OpenOrder units
abbrev j:Spec (CommRingCat.of O)⟶X:=ContactOverlapIntrinsic318.embedding units
abbrev p:X⟶Spec (CommRingCat.of ℚ):=ContactIntrinsicDifferentials318.structureMap units
abbrev M:X.Modules:=ContactIntrinsicDifferentials318.omega units
/-- The original canonical fifth pullback comparison, with the literal
Spec(OpenOrder), ambient Scheme and open presentation fixed explicitly.
Only presentation is made explicit; the global section and maps are unchanged. -/
theorem restrict:
    IntrinsicChartSections318.sectionMap (Y:=X) (R:=ℚ) (S:=O) j p
      (ContactOverlapIntrinsic318.over_Q units) FifthOverlapDifferentialEquation318.pulled=
    M.presheaf.map (homOfLE (show (j ''ᵁ (⊤:(Spec (CommRingCat.of O)).Opens))≤(⊤:X.Opens)
      from le_top)).op FifthActualDifferential318.differential:=by
  let f:X⟶WeierstrassGluing318.scheme A B:=FifthCompletedGlobal318.map
  let k:=WeierstrassGluing318.finiteChart A B
  let q:=WeierstrassGluing318.structureMap A B
  have hs:j≫f=Spec.map (CommRingCat.ofHom FifthSourceOverlap318.shortMap.toRingHom)≫k:=on_common
  have hv:=AffineChartPullbackScalars318.image_le f j k _ hs
  have hn:=congrArg (fun m=>m (WeierstrassAffineInvariant318.form A B discriminant_unit))
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p q
      FifthCompletedGlobal318.over_Q FifthSourceOverlap318.shortMap j k
      (ContactOverlapIntrinsic318.over_Q units) (WeierstrassAffineInvariant318.finite_structure A B)
      hs hv)
  change IntrinsicDifferentialSectionPullback318.value f p q _ _ _ hv
    (IntrinsicChartSections318.sectionMap k q _
      (WeierstrassAffineInvariant318.form A B discriminant_unit))=_ at hn
  rw [WeierstrassAffineInvariant318.form_section] at hn
  exact hn.symm.trans (IntrinsicDifferentialSectionPullback318.globalSection_restrict f p q
    FifthCompletedGlobal318.over_Q _ _ hv invariant)
end FifthCanonicalCommonRestriction318
