module
public import PELOriginalCandidateChartDomains318
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace PELOriginalChartSectionField318
open PELOriginalCubicRelationIdeal318 PELOriginalGradedSectionRing318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateChartDomains318
open PELOriginalLevelTheta318 HomogeneousQuotientChart318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
abbrev SectionField:=FractionRing (Ring τ hτ)
@[expose] def quotientIntoSections:QuotientRing (relations τ hτ)→+*Ring τ hτ:=
  RingHom.kerLift (presentation τ hτ).toRingHom
lemma quotientIntoSections_injective:Function.Injective (quotientIntoSections τ hτ):=
  RingHom.kerLift_injective _
@[expose] def quotientIntoField:QuotientRing (relations τ hτ)→+*SectionField τ hτ:=
  (algebraMap (Ring τ hτ) (SectionField τ hτ)).comp (quotientIntoSections τ hτ)
lemma quotientIntoField_mk(p:Equations):
    quotientIntoField τ hτ (Ideal.Quotient.mk (relations τ hτ) p)=
      algebraMap (Ring τ hτ) (SectionField τ hτ) (presentation τ hτ p):=rfl
lemma quotientIntoField_injective:Function.Injective (quotientIntoField τ hτ):=
  (IsFractionRing.injective _ _).comp (quotientIntoSections_injective τ hτ)
lemma denominator_nonzero:
    quotientIntoField τ hτ (Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X j))≠0:=by
  intro h
  apply variable_not_relation τ hτ j
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply quotientIntoField_injective τ hτ
  simpa only [map_zero] using h
lemma denominator_units(y:Submonoid.powers
    (Ideal.Quotient.mk (relations τ hτ) (MvPolynomial.X j))):
    IsUnit (quotientIntoField τ hτ y):=by
  obtain ⟨y,⟨n,rfl⟩⟩:=y
  rw [map_pow]
  exact (isUnit_iff_ne_zero.mpr (denominator_nonzero τ hτ j)).pow n

/-- Localization is mapped into the fraction field of the SAME full
original graded section ring. Every denominator is a genuinely nonzero
original cubic section, not a chosen formal variable in a new field. -/
@[expose] def localizedIntoField:LocalizedQuotient (relations τ hτ) j→+*SectionField τ hτ:=
  IsLocalization.lift (denominator_units τ hτ j)
lemma localizedIntoField_injective:Function.Injective (localizedIntoField τ hτ j):=by
  apply (IsLocalization.lift_injective_iff (denominator_units τ hτ j)).mpr
  intro x y
  constructor
  · intro h
    simpa only [IsLocalization.lift_eq] using congrArg (localizedIntoField τ hτ j) h
  · intro h
    rw [quotientIntoField_injective τ hτ h]
@[expose] def embedding:CoordinateChart τ hτ j→+*SectionField τ hτ:=
  (localizedIntoField τ hτ j).comp (degreeZero (relations τ hτ) j).subtype
lemma embedding_injective:Function.Injective (embedding τ hτ j):=
  (localizedIntoField_injective τ hτ j).comp Subtype.val_injective

lemma fraction_image(n:ℕ)(p:Equations)(hp:p.IsHomogeneous n):
    embedding τ hτ j ((quotientMap (relations τ hτ) j).rangeRestrict (fraction j n p hp))=
      algebraMap (Ring τ hτ) (SectionField τ hτ) (presentation τ hτ p)/
        algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ j)^n:=by
  change localizedIntoField τ hτ j (quotientMap (relations τ hτ) j (fraction j n p hp))=_
  rw [fraction_value]
  apply (IsLocalization.lift_mk'_spec (denominator_units τ hτ j) _ _ _).mpr
  simp only [quotientIntoField_mk,map_pow,variable_image]
  have hn:algebraMap (Ring τ hτ) (SectionField τ hτ) (generators τ hτ j)≠0:=by
    simpa only [quotientIntoField_mk,variable_image] using denominator_nonzero τ hτ j
  field_simp [pow_ne_zero n hn]

/-- Actual constants enter through the original degree-zero polynomial
inclusion, homogeneous chart map, and original quotient restriction. -/
@[expose] def scalarMap:ℂ→+*CoordinateChart τ hτ j:=
  (quotientMap (relations τ hτ) j).rangeRestrict.comp
    ((HomogeneousLocalization.fromZeroRingHom
      ComplexProjectiveMarkerPoint318.grading (Submonoid.powers (MvPolynomial.X j))).comp
      ComplexProjectiveBase318.constants.toRingHom)
instance chartComplexAlgebra:Algebra ℂ (CoordinateChart τ hτ j):=(scalarMap τ hτ j).toAlgebra
lemma scalar_fraction(c:ℂ):scalarMap τ hτ j c=
    (quotientMap (relations τ hτ) j).rangeRestrict
      (fraction j 0 (MvPolynomial.C c) (MvPolynomial.isHomogeneous_C (Label 3) c)):=rfl
lemma embedding_scalar(c:ℂ):
    embedding τ hτ j (algebraMap ℂ (CoordinateChart τ hτ j) c)=
      algebraMap ℂ (SectionField τ hτ) c:=by
  change embedding τ hτ j (scalarMap τ hτ j c)=_
  rw [scalar_fraction,fraction_image]
  simp only [pow_zero,div_one,presentation,MvPolynomial.aeval_C]
  exact IsScalarTower.algebraMap_apply ℂ (Ring τ hτ) (SectionField τ hτ) c
@[expose] def algebraEmbedding:CoordinateChart τ hτ j→ₐ[ℂ]SectionField τ hτ:=
  {embedding τ hτ j with commutes':=embedding_scalar τ hτ j}
end PELOriginalChartSectionField318
