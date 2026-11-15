module
public import PELOriginalFiniteNativeNegation318
public section
noncomputable section
namespace PELOriginalWholeNativeNegation318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalDescendedLabelMaps318
open PELOriginalDescendedCharacterKernel318 OriginalContactInertiaBasis318

/-- Extend the actual ring-level comparison across EVERY omitted point
by schematic density and the original complex structure maps. -/
lemma whole_native_square (i:Fin 4):
    schemeDeck (toggle i)≫morphism i=
    morphism i≫GluedNegation318.negation (A i) (B i):=by
  letI:=NormalizedLegendreProjectiveModel318.separated
    (PELOriginalOrderedCharacterCoordinate318.parameter i)
  apply FourRootSchematicDensity318.ext branches branches_injective
    (NormalizedLegendreProjectiveModel318.structure (PELOriginalOrderedCharacterCoordinate318.parameter i))
  · rw [Category.assoc,PELOriginalWholeCharacterMorphisms318.over_complex,
      FourRootSchemeSignAction318.over_base,Category.assoc,
      GluedNegation318.negation_over_base,PELOriginalWholeCharacterMorphisms318.over_complex]
  · rw [←Category.assoc,FourRootSchemeSignAction318.finite_action,Category.assoc,
      PELOriginalWholeCharacterMorphisms318.on_finite,←Category.assoc,
      PELOriginalWholeCharacterMorphisms318.on_finite]
    exact PELOriginalFiniteNativeNegation318.finite_native_square i

/-- The descended ORIGINAL residual involution is exactly the already
constructed native whole Weierstrass negation, not a conjugate or a map
having only the same branch count. -/
theorem residual_eq_native (i:Fin 4):
    (residual i).hom=GluedNegation318.negation (A i) (B i):=by
  apply cancel_original i
  exact (descended_square i (toggle i)).trans (whole_native_square i)

theorem all_labels_native (i:Fin 4) (a:PELOriginalMaximalQuotient318.Labels):
    descended i a=𝟙 (Curve i) ∨
      descended i a=GluedNegation318.negation (A i) (B i):=by
  simpa only [residual_eq_native] using descended_two_cases i a
end PELOriginalWholeNativeNegation318
