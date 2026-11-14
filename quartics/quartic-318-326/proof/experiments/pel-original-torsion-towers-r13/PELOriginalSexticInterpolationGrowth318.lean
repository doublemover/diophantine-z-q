module
public import PELOriginalSexticRootInterpolation318
public import LocalizedInterpolationWeightGrowth318
public section
noncomputable section
namespace PELOriginalSexticInterpolationGrowth318
open Polynomial PolynomialWeightBounds318 QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalSexticRootInterpolation318 PELOriginalSectionMultiplication318
open PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- Uniform growth of EVERY actual chart-element evaluation on all roots.
The polynomial expression is produced in the whole monogenic order. -/
theorem element_growth (hm : Q.Monic) (a : CoordinateChart τ hτ j) :
    Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖rootAlgebraPoint τ hτ j x d Q e he q a‖) := by
  obtain ⟨P,hP,hPeval⟩ := MonogenicOriginalCoordinates318.exists_expression
    (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) Q e he
    (algebraMap (CoordinateChart τ hτ j) _ a)
  have h := LocalizedRootWeightBounds318.polynomial d
    (fun q : OpenRoots d Q => q.val.val.1) (fun q => q.property) P
    (fun q => q.val.val.2) (LocalizedInterpolationWeightGrowth318.root_bound d Q hm)
  apply mono h
  intro q
  have hh := hPeval _ (rootPoint τ hτ j x d Q e he q)
  have hr : (rootPoint τ hτ j x d Q e he q).val (e (AdjoinRoot.root Q)) = q.val.val.2 :=
    candidatePoint_root τ hτ j x d Q e he _ q.property _ _
  rw [hr] at hh
  exact le_of_eq (congrArg norm hh)

/-- Compactness on the ORIGINAL torus and the actual coordinate formulas
give a uniform bound for the sextic value at EVERY independent root. -/
theorem value_growth (hm : Q.Monic) (s : homogeneous τ hτ 6)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖rootValue τ hτ j x d Q e he s q‖) := by
  classical
  let W := fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1
  have hW (q : OpenRoots d Q) : 1 ≤ W q := PrincipalOpenWeight318.one_le d q.val.val.1
  have hterms (i : Label 3) : Bounded W (fun q =>
      ‖rootAlgebraPoint τ hτ j x d Q e he q (ratioElement τ hτ j i)‖^2) :=
    pow (fun q => zero_le_one.trans (hW q))
      (element_growth τ hτ j x d Q e he hm (ratioElement τ hτ j i))
      (fun q => norm_nonneg _) 2
  obtain ⟨C,hC,hbound⟩ := rootValue_bound τ hτ j x d Q e he s honto
  exact mono (mul (fun q => zero_le_one.trans (hW q)) (const C)
    (sum hW Finset.univ _ (fun i _ => hterms i))
    (fun q => Finset.sum_nonneg (fun i _ => sq_nonneg _))) hbound

/-- Genuine uniform pole/growth bounds for ALL canonical interpolation
coefficients of each whole original sextic section. No normal generation,
regularity of a rational function, or branchwise estimate is assumed. -/
theorem coefficient_growth (hm : Q.Monic) (hs : Q.Separable) (s : homogeneous τ hτ 6)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ComplexVectors,
      ∀ hv : MvPolynomial.eval v d ≠ 0, ∀ n : ℕ,
      ‖MvPolynomial.eval v d ^ M *
        (interpolant τ hτ j x d Q e he hm s v).coeff n‖ ≤ C*(1+‖v‖)^N :=
  LocalizedInterpolationWeightGrowth318.pole_coefficients d Q hm hs
    (rootValue τ hτ j x d Q e he s) (value_growth τ hτ j x d Q e he hm s honto)
end PELOriginalSexticInterpolationGrowth318
