module
public import PELOriginalMonogenicOrder318
public import PELOriginalFiniteOpenBaseChange318
public import MonicSeparableEtale318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public section
noncomputable section
namespace PELOriginalMonogenicEtaleOpen318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalProjectedFiniteOpen318 PELOriginalCandidateAffineCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The actual polynomial-base principal open is smooth over the SAME
complex constants, with its inherited localization algebra structure. -/
theorem base_smooth (d : BasePolynomial) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Localization.Away d)))) := by
  letI : Algebra.Smooth ℂ BasePolynomial := {}
  letI : Algebra.Smooth BasePolynomial (Localization.Away d) :=
    Algebra.Smooth.of_isLocalization_Away d
  letI : Algebra.Smooth ℂ (Localization.Away d) :=
    Algebra.Smooth.comp ℂ BasePolynomial (Localization.Away d)
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The produced WHOLE monogenic principal open is genuinely etale over
its actual projected base, and smooth over the original complex base.
The open immersion is into the SAME original projective candidate.
This asserts no smoothness at points outside the produced open. -/
theorem exists_etale_smooth_open (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, d ≠ 0 ∧ polynomialMap τ hτ j x d ≠ 0 ∧
      IsOpenImmersion (localizedChart τ hτ j x d) ∧
      Etale (localizedProjection τ hτ j x d) ∧
      Smooth (localizedChart τ hτ j x d ≫
        PELOriginalProperComplexCandidate318.structureMap τ hτ) := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,he,hbase⟩ :=
    PELOriginalMonogenicOrder318.exists_original_order_equiv τ hτ j x hx
  let g := Localization.awayMap (polynomialMap τ hτ j x).toRingHom d
  have hg : g.Etale := MonicSeparableEtale318.of_ringEquiv g Q hm hs e hbase
  haveI hp : Etale (localizedProjection τ hτ j x d) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  haveI hb := base_smooth d
  refine ⟨d,hd,ha,PELOriginalFiniteOpenBaseChange318.actual_open_immersion
    τ hτ j x d,hp,?_⟩
  rw [PELOriginalFiniteOpenBaseChange318.original_complex_base,
    ←PELOriginalFiniteOpenBaseChange318.projection_over_complex_base τ hτ j x d]
  infer_instance
end PELOriginalMonogenicEtaleOpen318
