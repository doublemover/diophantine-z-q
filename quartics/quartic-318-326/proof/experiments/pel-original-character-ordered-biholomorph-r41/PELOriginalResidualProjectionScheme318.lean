module
public import FourRootProjectiveDeckInvariance318
public import PELOriginalResidualBranchPoints318
public section
noncomputable section
namespace PELOriginalResidualProjectionScheme318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalKernelStableOpens318 PELOriginalDescendedLabelMaps318
open PELOriginalDescendedCharacterKernel318 PELOriginalOrderedCharacterCoordinate318
open PELOriginalNormalizedBaseSchemeSquare318 PELOriginalOrderedBaseSchemeNormalization318

/-- Genuine equality of Scheme maps for all original descended labels,
not just invariance after evaluation at closed complex points. -/
theorem descended_projection (i:Fin 4) (a:PELOriginalMaximalQuotient318.Labels):
    descended i a≫NormalizedLegendreSchemeProjection318.projection (parameter i)=
      NormalizedLegendreSchemeProjection318.projection (parameter i):=by
  apply cancel_original i
  rw [←Category.assoc,descended_square,Category.assoc,whole_square,
    ←Category.assoc,FourRootProjectiveDeckInvariance318.whole_projection_invariant
      branches branches_injective]

theorem residual_projection (i:Fin 4):
    (residual i).hom≫NormalizedLegendreSchemeProjection318.projection (parameter i)=
      NormalizedLegendreSchemeProjection318.projection (parameter i):=
  descended_projection i (PELOriginalCharacterQuotient318.toggle i)

/-- Naturality over arbitrary test schemes, including nonreduced tests.
This is map invariance, not an unproved categorical double quotient. -/
theorem test_scheme_invariance (i:Fin 4) {T:Scheme} (p:T⟶Curve i):
    (p≫(residual i).hom)≫NormalizedLegendreSchemeProjection318.projection (parameter i)=
      p≫NormalizedLegendreSchemeProjection318.projection (parameter i):=by
  rw [Category.assoc,residual_projection]

/-- On every original source test point all four normalized projections
factor through the SAME original projective base with the exact specified
ordered affine changes. No lift from an analytic point is assumed. -/
theorem source_test_square (i:Fin 4) {T:Scheme}
    (p:T⟶FourRootGluedScheme318.scheme branches):
    (p≫morphism i)≫NormalizedLegendreSchemeProjection318.projection (parameter i)=
      (p≫FourRootProjectiveProjection318.projection branches)≫(baseNormalization i).hom:=by
  rw [Category.assoc,whole_square,Category.assoc]
end PELOriginalResidualProjectionScheme318
