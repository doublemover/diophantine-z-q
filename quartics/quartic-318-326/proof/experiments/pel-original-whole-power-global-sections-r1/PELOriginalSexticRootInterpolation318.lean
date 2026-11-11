module
public import PELOriginalSexticRatioGrowth318
public import LocalizedRootInterpolation318
public import PELOriginalFullLocalizedPoints318
public section
noncomputable section
namespace PELOriginalSexticRootInterpolation318
open Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalCandidatePointEquivalence318 PELOriginalSexticChartRatios318
open PELOriginalSexticRatioCover318 PELOriginalSectionMultiplication318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- Every independent root gives an ordinary point of the WHOLE original
chart, preserving its actual complex coefficient map. -/
@[expose] def rootAlgebraPoint (q : OpenRoots d Q) : CoordinateChart τ hτ j →ₐ[ℂ] ℂ where
  __ := (rootPoint τ hτ j x d Q e he q).val.comp
    (algebraMap (CoordinateChart τ hτ j) (Localization.Away (polynomialMap τ hτ j x d)))
  commutes' c := rootPoint_scalar τ hτ j x d Q e he q c

@[expose] def rootLocusPoint (q : OpenRoots d Q) : Locus τ hτ j :=
  toLocus τ hτ j (rootAlgebraPoint τ hτ j x d Q e he q)

lemma rootLocusPoint_coordinates (q : OpenRoots d Q) :
    (rootLocusPoint τ hτ j x d Q e he q).val = coordinates τ hτ j x d Q e he q := by
  funext a
  rfl

lemma rootLocusPoint_original (z : originalDomain τ hτ j x d) :
    rootLocusPoint τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z) =
      (⟨PELOriginalAllLevelHolomorphicMap318.ratioVector τ hτ 1 j z.val,
        PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j
          ⟨z.val,z.property.1,rfl⟩⟩ : Locus τ hτ j) := by
  apply Subtype.ext
  rw [rootLocusPoint_coordinates,coordinates_original]

@[expose] def rootValue (s : homogeneous τ hτ 6) (q : OpenRoots d Q) : ℂ :=
  candidateRatio τ hτ j s (rootLocusPoint τ hτ j x d Q e he q)

lemma rootValue_original (s : homogeneous τ hτ 6) (z : originalDomain τ hτ j x d) :
    rootValue τ hτ j x d Q e he s (originalOpenRootPoint τ hτ j x d Q e he z) =
      coverRatio τ hτ j s z.val := by
  rw [rootValue,rootLocusPoint_original,candidate_original]

/-- One canonical polynomial in the actual primitive root, using the
sextic value on EVERY root in the full candidate fiber. Its coefficients
are honest scalar functions on the fixed base open, not yet localized
ring elements. -/
@[expose] def interpolant (hm : Q.Monic) (s : homogeneous τ hτ 6) :
    ComplexVectors → Polynomial ℂ :=
  LocalizedRootInterpolation318.polynomial d Q hm (rootValue τ hτ j x d Q e he s)

/-- Exact recovery at every original point over the same produced open. -/
theorem interpolant_original (hm : Q.Monic) (s : homogeneous τ hτ 6)
    (z : originalDomain τ hτ j x d) :
    (interpolant τ hτ j x d Q e he hm s (projectedVector τ hτ j x z.val)).eval
      (primitiveValue τ hτ j x d Q e z.val) = coverRatio τ hτ j s z.val :=
  (LocalizedRootInterpolation318.evaluation d Q hm (rootValue τ hτ j x d Q e he s)
    (originalOpenRootPoint τ hτ j x d Q e he z)).trans
      (rootValue_original τ hτ j x d Q e he s z)

/-- Actual full-image exhaustion turns the compact section bound into
a bound on ALL interpolation values. Every signed ratio is evaluated by
the SAME full original chart point; no auxiliary branch is omitted. -/
theorem rootValue_bound (s : homogeneous τ hτ 6)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : OpenRoots d Q,
      ‖rootValue τ hτ j x d Q e he s q‖ ≤
        C * ∑ i : Label 3, ‖rootAlgebraPoint τ hτ j x d Q e he q
          (ratioElement τ hτ j i)‖^2 := by
  obtain ⟨C,hC,hbound⟩ := PELOriginalSexticRatioGrowth318.cover_ratio_bound τ hτ s
  refine ⟨C,hC,?_⟩
  intro q
  obtain ⟨z,rfl⟩ := honto q
  rw [rootValue_original]
  have hf := PELOriginalFullLocalizedPoints318.rootPoint_original τ hτ j x d Q e he z
  have hratio (i : Label 3) : rootAlgebraPoint τ hτ j x d Q e he
      (originalOpenRootPoint τ hτ j x d Q e he z) (ratioElement τ hτ j i) =
      value τ hτ 3 i z.val / value τ hτ 3 j z.val := by
    change (rootPoint τ hτ j x d Q e he _).val _ = _
    rw [hf,originalPoint_source,actual_ratio_evaluation]
  simpa only [hratio] using hbound j z.val z.property.1
end PELOriginalSexticRootInterpolation318
