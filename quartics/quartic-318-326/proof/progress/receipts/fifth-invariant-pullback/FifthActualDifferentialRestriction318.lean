module
public import FifthActualDifferential318
public section
noncomputable section
namespace FifthActualDifferentialRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthActualDifferential318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
/-- Actual canonical completed-map pullback, restricted to the full original
unbranched chart, equals its literal algebraic differential pullback. -/
theorem restrict:
    IntrinsicChartSections318.sectionMap (ContactOverlapIntrinsic318.embedding units)
      (ContactIntrinsicDifferentials318.structureMap units) (ContactOverlapIntrinsic318.over_Q units)
        FifthOverlapDifferentialEquation318.pulled=
    M.presheaf.map (homOfLE (show ContactOverlapIntrinsic318.embedding units ''ᵁ ⊤≤⊤
      from le_top)).op differential:=by
  let f:=FifthCompletedGlobal318.map
  let j:=ContactOverlapIntrinsic318.embedding units
  let k:=WeierstrassGluing318.finiteChart A B
  let p:=ContactIntrinsicDifferentials318.structureMap units
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
end FifthActualDifferentialRestriction318
