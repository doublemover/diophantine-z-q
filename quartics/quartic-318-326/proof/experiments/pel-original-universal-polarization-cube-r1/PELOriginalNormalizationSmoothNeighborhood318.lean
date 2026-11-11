module
public import PELOriginalNormalizationPrimitiveCertificate318
public import PELOriginalDerivativeOpenCharts318
public import FiniteNormalDerivativeSmoothNeighborhood318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace PELOriginalNormalizationSmoothNeighborhood318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartPrimitiveSeparator318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Literal minimal-polynomial derivative in the original chart ring,
using precisely the GIVEN normalization scalar map. -/
@[expose] def derivativeElement {n : ℕ}
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (t : CoordinateChart τ hτ j) : CoordinateChart τ hτ j :=
  letI : Algebra (MvPolynomial (Fin n) ℂ) (CoordinateChart τ hτ j) := g.toAlgebra
  Polynomial.aeval t (minpoly (MvPolynomial (Fin n) ℂ) t).derivative

/-- One SAME original ratio element separates the entire chosen finite
fiber, and its literal derivative open gives a genuine smooth original
candidate neighborhood of every actual point where that derivative is
nonzero. The finite fraction-field structure and primitive generator
are PRODUCED from g, not supplied as external assumptions. Pointwise
nonvanishing is the sole remaining local input to this consumer. -/
theorem exists_fiber_smooth_neighborhoods {n : ℕ}
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite)
    (v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    ∃ c : ℂ,
      Set.InjOn (fun f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ =>
        f (weightedRatioElement τ hτ j c))
        {f | ∀ r : MvPolynomial (Fin n) ℂ, f (g r) = v r} ∧
      let d := derivativeElement τ hτ j g (weightedRatioElement τ hτ j c)
      IsOpenImmersion (PELOriginalDerivativeOpenCharts318.inclusion τ hτ j d) ∧
      Smooth (PELOriginalDerivativeOpenCharts318.inclusion τ hτ j d ≫
        PELOriginalProperComplexCandidate318.structureMap τ hτ) ∧
      ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ, f d ≠ 0 →
        ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away d)),
          u ≫ PELOriginalDerivativeOpenCharts318.inclusion τ hτ j d =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ chartMap τ hτ j := by
  let R := MvPolynomial (Fin n) ℂ
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
  obtain ⟨c,hprimitive,hsep⟩ := exists_primitive_fiber_separator τ hτ j R K v
  let t := weightedRatioElement τ hτ j c
  let d := derivativeElement τ hτ j g t
  have hE : Algebra.Etale R (Localization.Away d) := by
    simpa only [FiniteNormalPrimitiveConductor318.embedding_mk] using
      FiniteNormalDerivativeEtale318.whole_derivative_open_etale R K A L t hprimitive
  letI := hE
  letI : Algebra.Smooth ℂ (Localization.Away d) :=
    Algebra.Smooth.comp ℂ R (Localization.Away d)
  refine ⟨c,hsep,PELOriginalDerivativeOpenCharts318.open_immersion τ hτ j d,?_,?_⟩
  · rw [PELOriginalDerivativeOpenCharts318.original_complex_base]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  · intro f hfd
    have hlocal :
        IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d)))) ∧
        Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away d)))) ∧
        ∃ u : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away d)),
          u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away d))) =
            Spec.map (CommRingCat.ofHom f.toRingHom) := by
      simpa only [FiniteNormalPrimitiveConductor318.embedding_mk] using
        FiniteNormalDerivativeSmoothNeighborhood318.point_has_smooth_open
          R K A L t hprimitive f hfd
    obtain ⟨u,hu⟩ := hlocal.2.2
    refine ⟨u,?_⟩
    rw [PELOriginalDerivativeOpenCharts318.inclusion,←Category.assoc,hu]
end PELOriginalNormalizationSmoothNeighborhood318
