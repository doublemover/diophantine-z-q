module
public import FiniteNormalDerivativeNormalOpen318
public import PELOriginalCandidateSmooth318
public section
noncomputable section
namespace PELOriginalNormalSmoothNeighborhood318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateNineChartCover318 PELOriginalChartPrimitiveSeparator318
open PELOriginalDerivativeOpenCharts318 PELOriginalReducedProjectiveCandidate318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance chartDomain (j : Label 3) : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Every actual original point has a principal neighborhood that is
both genuinely smooth and an ACTUAL integrally closed whole ring. The
normality proof uses the same primitive conductor and does not depend
on treating analytic and algebraic local rings as identical. -/
theorem original_point (j : Label 3) (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : CoordinateChart τ hτ j,
      algebraEvaluation τ hτ x j hx d ≠ 0 ∧
      IsIntegrallyClosed (Localization.Away d) ∧
      IsOpenImmersion (inclusion τ hτ j d) ∧
      Smooth (inclusion τ hτ j d ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ) ∧
      ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away d)),
        u ≫ inclusion τ hτ j d =
          Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ x j hx).toRingHom) ≫
            chartMap τ hτ j := by
  obtain ⟨g,hf,hg,hjet,e,he,hxe,hi⟩ :=
    PELOriginalFiniteUnramifiedProjection318.exists_finite_faithful_identity_chart τ hτ j x hx
  let R := MvPolynomial (Fin 2) ℂ
  let A := CoordinateChart τ hτ j
  let K := FractionRing R
  let L := FractionRing A
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : Module.Finite R A := hf
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : Module.Finite K L := WholeFiniteFractionExtension318.finite R A
  letI : Algebra.Smooth ℂ R := {}
  let f := algebraEvaluation τ hτ x j hx
  obtain ⟨c,hprimitive,hsep⟩ := exists_primitive_fiber_separator τ hτ j R K (f.comp g)
  let t := weightedRatioElement τ hτ j c
  let d := PELOriginalNormalizationSmoothNeighborhood318.derivativeElement τ hτ j g t
  have hfd : f d ≠ 0 :=
    PELOriginalSeparatingDerivativeNonzero318.derivative_nonzero τ hτ j g hg hf x hx e he hxe t hsep
  have hd : d ≠ 0 := fun hz => hfd (hz ▸ map_zero f)
  have hnormal : IsIntegrallyClosed (Localization.Away d) :=
    FiniteNormalDerivativeNormalOpen318.integrallyClosed R A t hprimitive hd
  letI : Smooth (PELOriginalProperComplexCandidate318.structureMap τ hτ) :=
    PELOriginalCandidateSmooth318.smooth τ hτ
  have hlocal := FiniteNormalDerivativeSmoothNeighborhood318.point_has_smooth_open
    R K A L t hprimitive f
    (show f (FiniteNormalBaseMonogenicSuborder318.embedding R A t
      (AdjoinRoot.mk (minpoly R t) (minpoly R t).derivative)) ≠ 0 by
      simpa only [FiniteNormalPrimitiveConductor318.embedding_mk] using hfd)
  obtain ⟨u,hu⟩ := hlocal.2.2
  refine ⟨d,hfd,hnormal,PELOriginalDerivativeOpenCharts318.open_immersion τ hτ j d,?_,u,?_⟩
  · infer_instance
  · rw [PELOriginalDerivativeOpenCharts318.inclusion,←Category.assoc]
    have hu' : u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d))) =
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
      simpa only [FiniteNormalPrimitiveConductor318.embedding_mk] using hu
    rw [hu']
end PELOriginalNormalSmoothNeighborhood318
