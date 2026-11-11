module
public import WholeFiniteFractionExtension318
public import PELOriginalChartPrimitiveSeparator318
public section
noncomputable section
namespace PELOriginalNormalizationPrimitiveCertificate318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartPrimitiveSeparator318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- One exact certificate from ANY chosen whole finite faithful
polynomial normalization and chosen base evaluation: genuine finite
fraction-field map, its original coefficient square, one original
ratio element polynomial-generating that field, and separation of the
ENTIRE chosen base fiber. No external finite-field structure remains. -/
theorem exists_certificate {n : ℕ}
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite)
    (v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) :
    ∃ φ : FractionRing (MvPolynomial (Fin n) ℂ) →ₐ[ℂ]
        FractionRing (CoordinateChart τ hτ j),
      φ.toRingHom.comp (algebraMap (MvPolynomial (Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n) ℂ))) =
        (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))).comp
          g.toRingHom ∧
      φ.toRingHom.Finite ∧
      ∃ c : ℂ,
        Function.Surjective (Polynomial.eval₂RingHom φ.toRingHom
          (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))
            (weightedRatioElement τ hτ j c))) ∧
        Set.InjOn (fun f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ =>
          f (weightedRatioElement τ hτ j c))
          {f | ∀ r : MvPolynomial (Fin n) ℂ, f (g r) = v r} := by
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
  let φ : K →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ K L
  obtain ⟨c,hc,hsep⟩ := exists_primitive_fiber_separator τ hτ j R K v
  refine ⟨φ,?_,?_,c,?_,hsep⟩
  · exact WholeFiniteFractionExtension318.coefficient_square R A
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact hc
end PELOriginalNormalizationPrimitiveCertificate318
