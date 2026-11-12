module
public import PELOriginalFullPrimitiveOpen318
public import LocalizedComplexPointBase318
public section
noncomputable section
namespace PELOriginalFullLocalizedPoints318
open Polynomial Set AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
open PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)
variable (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he))

lemma rootPoint_original (z : originalDomain τ hτ j x d) :
    (rootPoint τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z)).val =
      (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val := by
  have hf : rootPoint τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z) =
      originalPoint τ hτ j x z.val z.property.1 d z.property.2 := by
    apply candidatePoint_eq
    exact (primitiveValue_eq τ hτ j x d Q e z.val z.property.1 z.property.2).symm
  exact congrArg Subtype.val hf

/-- EVERY full localized candidate evaluation over every actual base
point is the actual original theta evaluation on ALL ring elements,
including inverse denominators. The projected base vector is unchanged. -/
theorem every_fiber_point (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0)
    (f : BasePreservingAffinePoints318.Points
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d v hv)) :
    ∃ z : originalDomain τ hτ j x d,
      projectedVector τ hτ j x z.val = v ∧
      f.val = (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val := by
  let r := AdjoinRootSpecializedPoints318.rootEquiv Q
    (ComplexPolynomialOpenPoints318.evaluation d v hv)
    (BasePreservingAffinePoints318.monogenicPointsEquiv _ _ Q e he f)
  let q : OpenRoots d Q :=
    ⟨⟨(v,r.val),(LocalizedPrimitiveRootChart318.equation_on_open d Q v hv r.val).trans r.property⟩,hv⟩
  have hqf : (rootPoint τ hτ j x d Q e he q).val = f.val := by
    apply congrArg Subtype.val
    apply candidatePoint_eq
    rfl
  obtain ⟨z,hz⟩ := honto q
  refine ⟨z,congrArg (fun q : OpenRoots d Q => q.val.val.1) hz,?_⟩
  rw [←hz,rootPoint_original] at hqf
  exact hqf.symm

/-- Ordinary complex algebra points have the required full base square
constructed automatically. No selected point or base-preserving premise
is supplied by the caller. -/
theorem every_complex_point
    (f : Localization.Away (polynomialMap τ hτ j x d) →ₐ[ℂ] ℂ) :
    ∃ z : originalDomain τ hτ j x d,
      f.toRingHom = (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val := by
  obtain ⟨v,hv,hf⟩ := LocalizedComplexPointBase318.exists_base (polynomialMap τ hτ j x) d f
  obtain ⟨z,hbase,hz⟩ := every_fiber_point τ hτ j x d Q e he honto v hv ⟨f.toRingHom,hf⟩
  exact ⟨z,hz⟩

/-- The same result for actual Spec(C)-valued fiber points, using the
proved full-faithful Spec equivalence rather than only underlying points. -/
theorem every_scheme_fiber_point (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0)
    (p : BasePreservingAffinePoints318.SchemePoints
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d v hv)) :
    ∃ z : originalDomain τ hτ j x d,
      projectedVector τ hτ j x z.val = v ∧
      p.val = Spec.map (CommRingCat.ofHom
        (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val) := by
  obtain ⟨f,rfl⟩ := (BasePreservingAffinePoints318.toScheme_bijective _ _).2 p
  obtain ⟨z,hbase,hf⟩ := every_fiber_point τ hτ j x d Q e he honto v hv f
  refine ⟨z,hbase,?_⟩
  change Spec.map (CommRingCat.ofHom f.val) = _
  rw [hf]
/-- An ordinary point of the unlocalized original chart lying on the
same produced principal open is the actual theta evaluation on every
chart element. Localization is constructed from its nonzero value. -/
theorem every_chart_point (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ)
    (hf : f (polynomialMap τ hτ j x d) ≠ 0) :
    ∃ z : originalDomain τ hτ j x d,
      ∀ a : CoordinateChart τ hτ j,
        f a = algebraEvaluation τ hτ z.val j z.property.1 a := by
  let F : Localization.Away (polynomialMap τ hτ j x d) →ₐ[ℂ] ℂ :=
    IsLocalization.Away.liftAlgHom (polynomialMap τ hτ j x d) (isUnit_iff_ne_zero.mpr hf)
  obtain ⟨z,hz⟩ := every_complex_point τ hτ j x d Q e he honto F
  refine ⟨z,?_⟩
  intro a
  have ha := congrArg (fun f : Localization.Away (polynomialMap τ hτ j x d) →+* ℂ =>
    f (algebraMap (CoordinateChart τ hτ j) _ a)) hz
  simpa only [F,IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq,originalPoint_source] using ha

/-- An unconditional actual-original consumer: the denominator is
produced by the full primitive-open theorem, and every ordinary chart
point there is realized on the entire original chart ring. -/
theorem exists_full_chart_open (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, d ≠ 0 ∧ polynomialMap τ hτ j x d ≠ 0 ∧
      ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
        f (polynomialMap τ hτ j x d) ≠ 0 →
          ∃ z : originalDomain τ hτ j x d,
            ∀ a : CoordinateChart τ hτ j,
              f a = algebraEvaluation τ hτ z.val j z.property.1 a := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he,honto⟩ :=
    PELOriginalFullPrimitiveOpen318.exists_full_original_open τ hτ j x hx
  exact ⟨d,hd,ha,fun f hf => every_chart_point τ hτ j x d Q e he honto f hf⟩
end PELOriginalFullLocalizedPoints318
