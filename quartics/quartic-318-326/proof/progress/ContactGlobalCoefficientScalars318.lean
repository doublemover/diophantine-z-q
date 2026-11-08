module
public import ContactGlobalDifferentialCoefficient318
public section
noncomputable section
namespace ContactGlobalCoefficientScalars318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthOverlapCoordinates318 FifthSignRestriction318 ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
lemma form_smul (a:ℚ) (s:Γ(M,⊤)):
    form (ContactCharacterGlobalIndependence318.constants a • s)=algebraMap ℚ O a • form s:=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p
    (ContactOverlapIntrinsic318.over_Q units)).injective
  rw [form_restrict,Scheme.Modules.map_smul,FifthGlobalIndependence318.constants_restrict,
    IntrinsicChartSections318.section_smul,form_restrict]
  rfl
/-- Constants are the actual source structural functions, not a separately
chosen Q-module structure on the space of global sections. -/
theorem coefficient_smul (a:ℚ) (s:Γ(M,⊤)):
    coefficient (ContactCharacterGlobalIndependence318.constants a • s)=
      algebraMap ℚ L a * coefficient s:=by
  rw [coefficient_apply,form_smul,map_smul,smul_eq_mul,map_mul,RingHom.map_rat_algebraMap]
  rfl
/-- The whole-open coefficient detects actual global intrinsic sections
through the established integral five-chart detection theorem. -/
theorem coefficient_injective:Function.Injective coefficient:=by
  intro s t h
  apply ContactGlobalSectionDetection318.restrict_injective units
  rw [←form_restrict,←form_restrict]
  congr 1
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  exact h
end ContactGlobalCoefficientScalars318
