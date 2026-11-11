module
public import PELOriginalRootCoordinates318
public import PELOriginalClosedAffineImage318
public import PELOriginalRatioEvaluationExt318
public section
noncomputable section
namespace PELOriginalClopenPrimitiveSheets318
open Set Filter Polynomial
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLocalizedEvaluationSquare318
open PELOriginalPrimitiveLocalReconstruction318 PELOriginalOpenPrimitiveSheets318
open PELOriginalRootCoordinates318 PELOriginalClosedAffineImage318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The exact missing comparison: an independent root has original
coordinates in the actual theta image if and only if that SAME root
comes from an actual original point. Whole-ring coordinate extensionality
recovers the primitive value, including its inverse denominators. -/
theorem selected_eq_preimage :
    Set.range (originalOpenRootPoint τ hτ j x d Q e he) =
      (coordinates τ hτ j x d Q e he) ⁻¹' affineImage τ hτ j := by
  ext q
  constructor
  · rintro ⟨z,rfl⟩
    change coordinates τ hτ j x d Q e he (originalOpenRootPoint τ hτ j x d Q e he z) ∈
      affineImage τ hτ j
    rw [coordinates_original]
    exact ⟨z.val,z.property.1,rfl⟩
  · rintro ⟨z,hz,hcoord⟩
    have hbase : projectedVector τ hτ j x z = q.val.val.1 := by
      rw [←coordinates_projection τ hτ j x d Q e he q]
      change PELOriginalLevelThreeLocalImage318.localProjection τ hτ x j
        (ratioVector τ hτ 1 j z) = _
      rw [hcoord]
    have hv : MvPolynomial.eval (projectedVector τ hτ j x z) d ≠ 0 := by
      rw [hbase]
      exact q.property
    have hpoint : (rootPoint τ hτ j x d Q e he q).val =
        (originalPoint τ hτ j x z hz d hv).val := by
      apply PELOriginalRatioEvaluationExt318.localized_ringHom_ext_coordinates
        τ hτ j (polynomialMap τ hτ j x d)
      · intro c
        rw [rootPoint_scalar,originalPoint_source]
        exact ((algebraEvaluation τ hτ z j hz).commutes c).symm
      · intro a
        rw [originalPoint_source,coordinate_evaluation]
        exact (congrFun hcoord a).symm
    have hroot : (rootPoint τ hτ j x d Q e he q).val (e (AdjoinRoot.root Q)) =
        q.val.val.2 := candidatePoint_root τ hτ j x d Q e he _ q.property _ _
    have hb : primitiveValue τ hτ j x d Q e z = q.val.val.2 := by
      rw [primitiveValue_eq τ hτ j x d Q e z hz hv]
      rw [←hpoint]
      exact hroot
    let w : originalDomain τ hτ j x d := ⟨z,hz,hv⟩
    refine ⟨w,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hbase hb

/-- Genuine closedness of the selected roots, in the actual WHOLE root
locus over D(d), now follows from the proved same-point comparison. -/
theorem selected_closed :
    IsClosed (Set.range (originalOpenRootPoint τ hτ j x d Q e he)) := by
  rw [selected_eq_preimage]
  exact (affineImage_closed τ hτ j).preimage (coordinates_continuous τ hτ j x d Q e he)

/-- The already proved ambient-root openness restricts to the same
independent principal-open root locus. -/
theorem selected_open (hs : Q.Separable) :
    IsOpen (Set.range (originalOpenRootPoint τ hτ j x d Q e he)) := by
  have hset : Set.range (originalOpenRootPoint τ hτ j x d Q e he) =
      (fun q : OpenRoots d Q => q.val) ⁻¹'
        Set.range (originalRootPoint τ hτ j x d Q e he) := by
    ext q
    constructor
    · rintro ⟨z,rfl⟩
      exact Set.mem_range_self z
    · rintro ⟨z,hz⟩
      exact ⟨z,Subtype.ext hz⟩
  rw [hset]
  exact (original_sheets_open τ hτ j x d Q e he hs).preimage continuous_subtype_val

/-- Nonemptiness is retained on the SAME produced denominator; clopen
does not yet mean the selected subset exhausts all candidate roots. -/
theorem selected_nonempty (hx : value τ hτ 3 j x ≠ 0) (hd : d ≠ 0) :
    (Set.range (originalOpenRootPoint τ hτ j x d Q e he)).Nonempty := by
  obtain ⟨q,z,hz⟩ := original_sheets_nonempty τ hτ j x d Q e he hx hd
  exact ⟨originalOpenRootPoint τ hτ j x d Q e he z,Set.mem_range_self z⟩
end PELOriginalClopenPrimitiveSheets318
