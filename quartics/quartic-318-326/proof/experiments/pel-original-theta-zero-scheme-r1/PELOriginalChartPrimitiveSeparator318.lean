module
public import PrimitiveFinitePointSeparator318
public import FiniteAlgebraEvaluationFiber318
public import PELOriginalRatioEvaluationExt318
public import PELOriginalCandidateChartDomains318
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public section
noncomputable section
namespace PELOriginalChartPrimitiveSeparator318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalRatioEvaluationExt318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

@[expose] def indexedRatios : Fin (Fintype.card (Label 3)) → CoordinateChart τ hτ j :=
  fun i => ratioElement τ hτ j ((Fintype.equivFin (Label 3)).symm i)

lemma indexed_ratios_generate : Function.Surjective
    (MvPolynomial.aeval (indexedRatios τ hτ j) :
      MvPolynomial (Fin (Fintype.card (Label 3))) ℂ →ₐ[ℂ] CoordinateChart τ hτ j) := by
  let e := MvPolynomial.renameEquiv ℂ (Fintype.equivFin (Label 3))
  have he : (MvPolynomial.aeval (indexedRatios τ hτ j)).comp e.toAlgHom =
      MvPolynomial.aeval (ratioElement τ hτ j) := by
    ext i
    simp [e,indexedRatios]
  intro a
  obtain ⟨p,hp⟩ := polynomial_surjective τ hτ j a
  refine ⟨e p,?_⟩
  exact (congrArg (fun f : MvPolynomial (Label 3) ℂ →ₐ[ℂ] CoordinateChart τ hτ j => f p) he).trans hp

/-- The chosen primitive element remains a literal fixed polynomial-
weighted sum of the original nine chart ratio elements. -/
@[expose] def weightedRatioElement (c : ℂ) : CoordinateChart τ hτ j :=
  PrimitiveFinitePointSeparator318.element (indexedRatios τ hτ j) c

/-- For any genuine finite rational-base structure on the SAME original
chart fraction field, one original constant-weighted ratio combination
is both primitive in that field and separating on a specified finite
set of actual whole-chart complex evaluations. -/
theorem exists_primitive_separator
    (K : Type) [Field K] [Algebra ℂ K]
    [Algebra K (FractionRing (CoordinateChart τ hτ j))]
    [IsScalarTower ℂ K (FractionRing (CoordinateChart τ hτ j))]
    [FiniteDimensional K (FractionRing (CoordinateChart τ hτ j))]
    (V : Set (CoordinateChart τ hτ j →ₐ[ℂ] ℂ)) (hV : V.Finite) :
    ∃ c : ℂ,
      Function.Surjective (Polynomial.aeval
        (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))
          (weightedRatioElement τ hτ j c)) :
        Polynomial K →ₐ[K] FractionRing (CoordinateChart τ hτ j)) ∧
      Set.InjOn (fun v : CoordinateChart τ hτ j →ₐ[ℂ] ℂ =>
        v (weightedRatioElement τ hτ j c)) V := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  exact PrimitiveFinitePointSeparator318.exists_primitive_separator
    (K := K) (L := FractionRing (CoordinateChart τ hτ j)) (T := AlgebraicClosure K)
    (indexedRatios τ hτ j) (indexed_ratios_generate τ hτ j) V hV

/-- The finite set is now produced from the WHOLE finite normalization:
one original ratio combination is primitive and separates its ENTIRE
specified base fiber of actual complex evaluations. -/
theorem exists_primitive_fiber_separator
    (R K : Type) [CommRing R] [Algebra ℂ R]
    [Algebra R (CoordinateChart τ hτ j)] [IsScalarTower ℂ R (CoordinateChart τ hτ j)]
    [Module.Finite R (CoordinateChart τ hτ j)]
    [Field K] [Algebra ℂ K]
    [Algebra K (FractionRing (CoordinateChart τ hτ j))]
    [IsScalarTower ℂ K (FractionRing (CoordinateChart τ hτ j))]
    [FiniteDimensional K (FractionRing (CoordinateChart τ hτ j))]
    (v : R →ₐ[ℂ] ℂ) :
    ∃ c : ℂ,
      Function.Surjective (Polynomial.aeval
        (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))
          (weightedRatioElement τ hτ j c)) :
        Polynomial K →ₐ[K] FractionRing (CoordinateChart τ hτ j)) ∧
      Set.InjOn (fun f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ =>
        f (weightedRatioElement τ hτ j c))
        {f | ∀ r : R, f (algebraMap R (CoordinateChart τ hτ j) r) = v r} :=
  exists_primitive_separator τ hτ j K _
    (FiniteAlgebraEvaluationFiber318.finite (indexedRatios τ hτ j)
      (indexed_ratios_generate τ hτ j) v)
end PELOriginalChartPrimitiveSeparator318
