module
public import FifthActualDifferentialRestriction318
public import FifthInvariantScalar318
public import ContactGlobalSectionDetection318
public section
noncomputable section
namespace FifthGlobalPullbackNormalization318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthActualDifferential318 FifthInvariantScalar318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- The actual completed fifth quotient pulls its specified invariant back
to exactly -41160 times the already glued fifth global regular form. -/
theorem global_eq:differential=ContactCharacterGlobalIndependence318.constants scale •
    FifthGlobalDifferential318.differential:=by
  apply ContactGlobalSectionDetection318.restrict_injective units
  rw [←FifthActualDifferentialRestriction318.restrict,Scheme.Modules.map_smul,
    FifthGlobalIndependence318.constants_restrict,FifthGlobalIndependence318.restrict]
  exact (congrArg (IntrinsicChartSections318.sectionMap (ContactOverlapIntrinsic318.embedding units)
    (ContactIntrinsicDifferentials318.structureMap units) (ContactOverlapIntrinsic318.over_Q units))
      form_eq).trans (IntrinsicChartSections318.section_smul (ContactOverlapIntrinsic318.embedding units)
        (ContactIntrinsicDifferentials318.structureMap units) (ContactOverlapIntrinsic318.over_Q units)
        (algebraMap ℚ FifthOverlapCoordinates318.O scale) FifthGlobalIndependence318.form)
end FifthGlobalPullbackNormalization318
