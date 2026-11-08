module
public import FifthInfinityInvariantCoefficient318
public section
noncomputable section
namespace FifthInfinityInvariantRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 InfinityGlobalDifferentialRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The whole infinity expression is the literal restriction of the actual
canonical pullback along the actual completed fifth map. -/
theorem section_restrict:
    IntrinsicChartSections318.sectionMap j p overQ FifthInfinityInvariantCoefficient318.pulled=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op FifthActualDifferential318.differential:=by
  let f:=FifthCompletedGlobal318.map
  let k:=WeierstrassGluing318.finiteChart A B
  let q:=WeierstrassGluing318.structureMap A B
  have hs:j≫f=Spec.map (CommRingCat.ofHom FifthSourceInfinityAlgebra318.shortMap.toRingHom)≫k:=
    FifthCompletedGlobal318.on_infinity
  have hv:=AffineChartPullbackScalars318.image_le f j k _ hs
  have hn:=congrArg (fun m=>m (WeierstrassAffineInvariant318.form A B discriminant_unit))
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p q
      FifthCompletedGlobal318.over_Q FifthSourceInfinityAlgebra318.shortMap j k
      overQ (WeierstrassAffineInvariant318.finite_structure A B) hs hv)
  change IntrinsicDifferentialSectionPullback318.value f p q _ _ _ hv
    (IntrinsicChartSections318.sectionMap k q _
      (WeierstrassAffineInvariant318.form A B discriminant_unit))=_ at hn
  rw [WeierstrassAffineInvariant318.form_section] at hn
  exact hn.symm.trans (IntrinsicDifferentialSectionPullback318.globalSection_restrict f p q
    FifthCompletedGlobal318.over_Q _ _ hv FifthActualDifferential318.invariant)
theorem form_eq:form FifthActualDifferential318.differential=FifthInfinityInvariantCoefficient318.pulled:=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p overQ).injective
  rw [form_restrict,section_restrict]
/-- Exact actual global fifth invariant pullback on the entire infinity
chart, with a proved unit coefficient multiplying the literal u du. -/
theorem normalized:form FifthActualDifferential318.differential=
    (FifthInfinityInvariantCoefficient318.factor*InfinityOrderCoordinates318.coordinate units) •
      KaehlerDifferential.D ℚ I (InfinityOrderCoordinates318.coordinate units):=by
  rw [form_eq,FifthInfinityInvariantCoefficient318.normalized]
end FifthInfinityInvariantRestriction318
