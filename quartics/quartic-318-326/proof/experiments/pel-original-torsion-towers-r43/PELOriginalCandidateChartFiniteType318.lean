module
public import PELOriginalChartSectionField318
public section
noncomputable section
namespace PELOriginalCandidateChartFiniteType318
open PELOriginalCubicRelationIdeal318 PELOriginalCandidateAffineCharts318
open PELOriginalChartSectionField318 PELOriginalLevelTheta318 HomogeneousQuotientChart318
open ComplexProjectiveMarkerPoint318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
local instance standardGrading:GradedAlgebra (grading (ι:=Label 3)):=MvPolynomial.gradedAlgebra

/-- Finite type is proved for the ACTUAL scalar action on the same
literal degree-zero quotient chart. The original degree-zero base is
identified with C by its real constant inclusion, then the genuine
homogeneous localization finite-type theorem and the actual surjective
quotient restriction apply. No analytic-image/dimension theorem enters. -/
theorem finite_type:Algebra.FiniteType ℂ (CoordinateChart τ hτ j):=by
  haveI:Algebra.FiniteType (ComplexProjectiveBase318.DegreeZero (ι:=Label 3)) PELOriginalCubicRelationIdeal318.Equations:=
    ComplexProjectiveBase318.finite_type_zero
  haveI:Algebra.FiniteType (ComplexProjectiveBase318.DegreeZero (ι:=Label 3)) (Chart j):=
    HomogeneousLocalization.Away.finiteType (MvPolynomial.X j) 1
      (MvPolynomial.isHomogeneous_X ℂ j)
  have hzero:(HomogeneousLocalization.fromZeroRingHom
      (grading (ι:=Label 3)) (Submonoid.powers (MvPolynomial.X j))).FiniteType:=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hconst:(ComplexProjectiveBase318.constants (ι:=Label 3)).toRingHom.FiniteType:=
    RingHom.FiniteType.of_surjective _ ComplexProjectiveBase318.constants.surjective
  have hquot:((quotientMap (relations τ hτ) j).rangeRestrict).FiniteType:=
    RingHom.FiniteType.of_surjective _ (RingHom.rangeRestrict_surjective _)
  apply RingHom.finiteType_algebraMap.mp
  change (scalarMap τ hτ j).FiniteType
  exact hquot.comp (hzero.comp hconst)
end PELOriginalCandidateChartFiniteType318
