module
public import PELOriginalPolynomialGrowthFunction318
public section
noncomputable section
namespace PELOriginalFunctionRootInterpolation318
open Polynomial QuaternionicRealPeriod318 PolynomialWeightBounds318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedChartIndependence318
open PELOriginalProjectedFiniteOpen318 PELOriginalOpenPrimitiveSheets318
open PELOriginalSexticRootInterpolation318 PELOriginalPolynomialGrowthFunction318
open PELOriginalCandidatePointEquivalence318 PELOriginalRatioEvaluationExt318
open PELOriginalPrimitiveLocalReconstruction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

@[expose] def rootValue (F : Data τ hτ j) (q : OpenRoots d Q) : ℂ :=
  F.onCandidate (rootLocusPoint τ hτ j x d Q e he q)
lemma rootValue_original (F : Data τ hτ j) (z : originalDomain τ hτ j x d) :
    rootValue τ hτ j x d Q e he F (originalOpenRootPoint τ hτ j x d Q e he z)=F.onCover z.val := by
  rw [rootValue,rootLocusPoint_original]
  exact F.original z.val z.property.1

@[expose] def interpolant (hm : Q.Monic) (F : Data τ hτ j) : ComplexVectors → Polynomial ℂ :=
  LocalizedRootInterpolation318.polynomial d Q hm (rootValue τ hτ j x d Q e he F)
lemma interpolant_original (hm : Q.Monic) (F : Data τ hτ j)
    (z : originalDomain τ hτ j x d) :
    (interpolant τ hτ j x d Q e he hm F (projectedVector τ hτ j x z.val)).eval
      (primitiveValue τ hτ j x d Q e z.val)=F.onCover z.val :=
  (LocalizedRootInterpolation318.evaluation d Q hm (rootValue τ hτ j x d Q e he F)
    (originalOpenRootPoint τ hτ j x d Q e he z)).trans
      (rootValue_original τ hτ j x d Q e he F z)

/-- Polynomial coordinate growth controls values at EVERY independent
root. The point is the actual whole chart algebra homomorphism. -/
theorem value_growth (hm : Q.Monic) (F : Data τ hτ j) :
    Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖rootValue τ hτ j x d Q e he F q‖) := by
  classical
  let W := fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1
  have hW (q : OpenRoots d Q) : 1 ≤ W q := PrincipalOpenWeight318.one_le d q.val.val.1
  have hi (i : Label 3) : Bounded W (fun q =>
      ‖rootAlgebraPoint τ hτ j x d Q e he q (ratioElement τ hτ j i)‖) :=
    PELOriginalSexticInterpolationGrowth318.element_growth τ hτ j x d Q e he hm _
  have hsum : Bounded W (fun q => 1+∑ i : Label 3,
      ‖rootAlgebraPoint τ hτ j x d Q e he q (ratioElement τ hτ j i)‖) :=
    add hW (const 1) (sum hW Finset.univ _ (fun i _ => hi i))
  have hnonneg (q : OpenRoots d Q) : 0 ≤ 1+∑ i : Label 3,
      ‖rootAlgebraPoint τ hτ j x d Q e he q (ratioElement τ hτ j i)‖ := by positivity
  obtain ⟨C,hC,N,hb⟩ := F.growth
  exact mono (mul (fun q => zero_le_one.trans (hW q)) (const C)
    (pow (fun q => zero_le_one.trans (hW q)) hsum hnonneg N)
    (fun q => pow_nonneg (hnonneg q) N))
    (fun q => hb (rootAlgebraPoint τ hτ j x d Q e he q))

theorem coefficient_growth (hm : Q.Monic) (hs : Q.Separable) (F : Data τ hτ j) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ComplexVectors,
      ∀ hv : MvPolynomial.eval v d ≠ 0, ∀ n : ℕ,
      ‖MvPolynomial.eval v d ^ M *
        (interpolant τ hτ j x d Q e he hm F v).coeff n‖ ≤ C*(1+‖v‖)^N :=
  LocalizedInterpolationWeightGrowth318.pole_coefficients d Q hm hs
    (rootValue τ hτ j x d Q e he F) (value_growth τ hτ j x d Q e he hm F)
end PELOriginalFunctionRootInterpolation318
