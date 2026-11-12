module
public import PELOriginalOpenPrimitiveSheets318
public section
noncomputable section
namespace PELOriginalRootCoordinates318
open Set Filter Polynomial
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLocalizedEvaluationSquare318
open PELOriginalPrimitiveLocalReconstruction318 PELOriginalOpenPrimitiveSheets318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The entire independent root locus above the true common base open. -/
abbrev OpenRoots := {q : RootLocus d Q // MvPolynomial.eval q.val.1 d ≠ 0}

/-- Every root produces a point of the WHOLE original localized order,
using both inverse universal-property equivalences. -/
@[expose] def candidatePoint (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0)
    (z : ℂ) (hz : (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval z = 0) :
    BasePreservingAffinePoints318.Points
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d v hv) :=
  (BasePreservingAffinePoints318.monogenicPointsEquiv _ _ Q e he).symm
    ((AdjoinRootSpecializedPoints318.rootEquiv Q _).symm ⟨z,hz⟩)

lemma candidatePoint_root (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0)
    (z : ℂ) (hz : (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval z = 0) :
    (candidatePoint τ hτ j x d Q e he v hv z hz).val (e (AdjoinRoot.root Q)) = z := by
  change (AdjoinRootSpecializedPoints318.rootEquiv Q _
    (BasePreservingAffinePoints318.monogenicPointsEquiv _ _ Q e he
      (candidatePoint τ hτ j x d Q e he v hv z hz))).val = z
  rw [candidatePoint,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

lemma candidatePoint_eq (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0)
    (z : ℂ) (hz : (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval z = 0)
    (f : BasePreservingAffinePoints318.Points
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d v hv))
    (hf : f.val (e (AdjoinRoot.root Q)) = z) :
    candidatePoint τ hτ j x d Q e he v hv z hz = f := by
  apply (BasePreservingAffinePoints318.monogenicPointsEquiv _ _ Q e he).injective
  apply (AdjoinRootSpecializedPoints318.rootEquiv Q _).injective
  apply Subtype.ext
  exact (candidatePoint_root τ hτ j x d Q e he v hv z hz).trans hf.symm

@[expose] def rootPoint (q : OpenRoots d Q) :
    BasePreservingAffinePoints318.Points
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)
      (ComplexPolynomialOpenPoints318.evaluation d q.val.val.1 q.property) :=
  candidatePoint τ hτ j x d Q e he q.val.val.1 q.property q.val.val.2
    ((LocalizedPrimitiveRootChart318.equation_on_open d Q _ q.property _).symm.trans q.val.property)

/-- All original polynomial coefficients, including constants, are
retained by the whole candidate point over its actual root base. -/
lemma rootPoint_polynomial (q : OpenRoots d Q) (P : BasePolynomial) :
    (rootPoint τ hτ j x d Q e he q).val
      (algebraMap (CoordinateChart τ hτ j) _ (polynomialMap τ hτ j x P)) =
      MvPolynomial.eval q.val.val.1 P := by
  have h := congrArg (fun f : Localization.Away d →+* ℂ =>
    f (algebraMap BasePolynomial (Localization.Away d) P))
    (rootPoint τ hτ j x d Q e he q).property
  simpa only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,ComplexPolynomialOpenPoints318.evaluation_source] using h

lemma rootPoint_scalar (q : OpenRoots d Q) (c : ℂ) :
    (rootPoint τ hτ j x d Q e he q).val
      (algebraMap (CoordinateChart τ hτ j) _ (algebraMap ℂ (CoordinateChart τ hτ j) c)) = c := by
  simpa only [polynomialMap,MvPolynomial.aeval_C,MvPolynomial.eval_C] using
    rootPoint_polynomial τ hτ j x d Q e he q (MvPolynomial.C c)

/-- The whole candidate point's ORIGINAL affine chart coordinates. -/
@[expose] def coordinates (q : OpenRoots d Q) : TargetModel 1 := fun a =>
  (rootPoint τ hτ j x d Q e he q).val
    (algebraMap (CoordinateChart τ hτ j) _ (coordinateElement τ hτ j a))

/-- The coordinates recover the SAME fixed original base projection
for every independent root, not just for points already in the image. -/
lemma coordinates_projection (q : OpenRoots d Q) :
    PELOriginalLevelThreeLocalImage318.localProjection τ hτ x j
      (coordinates τ hτ j x d Q e he q) = q.val.val.1 := by
  funext k
  rw [projection_expansion]
  have h := rootPoint_polynomial τ hτ j x d Q e he q (MvPolynomial.X k)
  rw [polynomialMap_X,MvPolynomial.eval_X] at h
  simpa only [projectedFunction,map_sum,map_mul,rootPoint_scalar,coordinates] using h

/-- The coordinate map is genuinely continuous on ALL independent
roots on D(d), because each actual original coordinate has a fixed
polynomial expression over the original localized coefficient ring. -/
theorem coordinates_continuous : Continuous (coordinates τ hτ j x d Q e he) := by
  apply continuous_pi
  intro a
  obtain ⟨P,hP,hPeval⟩ := MonogenicOriginalCoordinates318.exists_expression
    (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) Q e he
    (algebraMap (CoordinateChart τ hτ j) _ (coordinateElement τ hτ j a))
  have hformula (q : OpenRoots d Q) : coordinates τ hτ j x d Q e he q a =
      LocalizedPrimitiveRootChart318.equation d P q.val.val := by
    have hh := hPeval _ (rootPoint τ hτ j x d Q e he q)
    have hr : (rootPoint τ hτ j x d Q e he q).val (e (AdjoinRoot.root Q)) = q.val.val.2 :=
      candidatePoint_root τ hτ j x d Q e he _ q.property _ _
    rw [LocalizedPrimitiveRootChart318.equation_on_open d P _ q.property _,Polynomial.eval_map]
    rw [hr] at hh
    exact hh
  apply continuous_iff_continuousAt.mpr
  intro q
  have ha := (LocalizedPrimitiveRootChart318.equation_analytic d P
    q.val.val.1 q.property q.val.val.2).continuousAt
  have hc := ha.comp (continuous_subtype_val.comp continuous_subtype_val).continuousAt
  exact hc.congr (Filter.Eventually.of_forall (fun w => (hformula w).symm))

@[expose] def originalOpenRootPoint (z : originalDomain τ hτ j x d) : OpenRoots d Q :=
  ⟨originalRootPoint τ hτ j x d Q e he z,z.property.2⟩

/-- On actual original points this map is EXACTLY the original full
ratio vector. No separate pointwise candidate model is substituted. -/
theorem coordinates_original (z : originalDomain τ hτ j x d) :
    coordinates τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z) =
      ratioVector τ hτ 1 j z.val := by
  have hf : rootPoint τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z) =
      originalPoint τ hτ j x z.val z.property.1 d z.property.2 := by
    apply candidatePoint_eq
    exact (primitiveValue_eq τ hτ j x d Q e z.val z.property.1 z.property.2).symm
  funext a
  change (rootPoint τ hτ j x d Q e he _).val _ = _
  rw [hf,originalPoint_source,coordinate_evaluation]
end PELOriginalRootCoordinates318
