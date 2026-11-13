module
public import FiniteNormalAlgebraProjection318
public import PELOriginalCandidateElementFunctions318
public import PELOriginalNormalizationBaseCutoff318
public section
noncomputable section
namespace PELOriginalCandidateNormalizationTopology318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateElementFunctions318
open PELOriginalCandidateAffineOpenImage318 PELOriginalProjectedChartIndependence318
open PELOriginalAllLevelHolomorphicMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- Actual whole-normalization base coordinates evaluated by fixed
polynomials on the original ambient affine model. -/
@[expose] def projection (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (w : TargetModel 1) : Fin n → ℂ :=
  fun k => elementValue τ hτ j (g (MvPolynomial.X k)) w

lemma projection_continuous (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j) :
    Continuous (projection τ hτ j n g) :=
  continuous_pi (fun k => elementValue_continuous τ hτ j (g (MvPolynomial.X k)))

/-- The complete base evaluation square, not only its coordinate
shadow. This uses the actual candidate evaluation and the same g. -/
lemma projection_square (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (w : Locus τ hτ j) :
    (toPoint τ hτ j w).comp g = MvPolynomial.aeval (projection τ hτ j n g w.val) := by
  ext k
  change toPoint τ hτ j w (g (MvPolynomial.X k)) =
    elementValue τ hτ j (g (MvPolynomial.X k)) w.val
  exact toPoint_value τ hτ j _ w

/-- EVERY faithful finite polynomial normalization of the WHOLE
original candidate chart has open projection in its literal ambient
Euclidean topology. No denominator or discriminant is inverted. -/
theorem projection_open (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite) :
    IsOpenMap (fun w : Locus τ hτ j => projection τ hτ j n g w.val) := by
  let R := MvPolynomial (Fin n) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : IsTorsionFree R A := isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : Module.Finite R A := hf
  apply FiniteNormalAlgebraProjection318.projection_open A
    (coordinateElement τ hτ j) (candidateLocus τ hτ j)
    (candidateLocus_closed τ hτ j) (toPoint τ hτ j)
    (toPoint_coordinate τ hτ j) (equivalence τ hτ j).symm.surjective
    (projection τ hτ j n g) (projection_continuous τ hτ j n g)
  intro w r
  exact congrArg (fun f : R →ₐ[ℂ] ℂ => f r) (projection_square τ hτ j n g w)

/-- Removing the preimage of ANY genuine nonzero normalization
polynomial leaves a Euclidean dense subset of the whole original
candidate, including all singular, collision and boundary points. -/
theorem dense_base_open (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite)
    (b : MvPolynomial (Fin n) ℂ) (hb : b ≠ 0) :
    Dense {w : Locus τ hτ j | MvPolynomial.eval (projection τ hτ j n g w.val) b ≠ 0} :=
  FiniteIntegralProjectionOpen318.dense_base_nonvanishing _ _
    (projection_open τ hτ j n g hg hf) b hb
end PELOriginalCandidateNormalizationTopology318
