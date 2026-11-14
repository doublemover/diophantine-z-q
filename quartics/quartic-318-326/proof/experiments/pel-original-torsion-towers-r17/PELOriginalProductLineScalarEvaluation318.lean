module
public import PELOriginalUniversalBalancedCoefficients318
public section
noncomputable section
namespace PELOriginalProductLineScalarEvaluation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalCandidateComplexPoints318 PELOriginalBalancedLineData318
open PELOriginalOpenRegularFunction318
variable (τ : ℂ) (hτ : 0 < τ.im) (D : PELOriginalBalancedLineData318.Data τ hτ)
variable {Y : Scheme} (f : Y ⟶ candidate τ hτ)

/-- Evaluate the ACTUAL pullback frame scalar on ANY original source
open. The original candidate point and full structure-sheaf square are
retained, so this applies to both projections, sum and difference. -/
lemma scalar_value (i j : NonemptyIndex τ hτ) (W : Y.Opens)
    (h : W≤f ⁻¹ᵁ (opens τ hτ i ⊓ opens τ hτ j))
    (p : Spec (CommRingCat.of ℂ) ⟶ W.toScheme) (z : ComplexVectors)
    (hp : p≫W.ι≫f=candidateComplexPoint τ hτ (projection (P τ) z)) :
    ComplexOpenPointEvaluation318.evaluation W p
      (LineFrameTransitions318.scalar ((Scheme.Modules.pullback f).obj D.M)
        (fun i => f ⁻¹ᵁ opens τ hτ i)
        (TranslatedLineIsoScalars318.targetFrame f D.M (opens τ hτ) D.frame)
        i j W (h.trans (f.preimage_mono inf_le_left))
          (h.trans (f.preimage_mono inf_le_right))).val=
      D.g j z/D.g i z := by
  have hz : z∈domain τ hτ (opens τ hτ i ⊓ opens τ hτ j) := by
    change candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ)∈_
    rw [←hp]
    exact h (p (IsLocalRing.closedPoint ℂ)).property
  let q := point τ hτ (opens τ hτ i ⊓ opens τ hτ j) z hz
  rw [TranslatedLineIsoScalars318.target_transition_subopen]
  change ComplexOpenPointEvaluation318.evaluation W p
    (Y.presheaf.map (homOfLE h).op (f.app _
      ((LineFrameCocycle318.cocycle D.M (opens τ hτ) D.frame).transition i j).val))=_
  rw [ComplexOpenPointEvaluation318.restriction]
  have he : (p≫Y.homOfLE h)≫(f ⁻¹ᵁ (opens τ hτ i ⊓ opens τ hτ j)).ι≫f=
      q≫(opens τ hτ i ⊓ opens τ hτ j).ι := by
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,point_ι]
    exact hp
  rw [ComplexOpenPointEvaluation318.pullback f _ _ q he]
  exact (value_at_point τ hτ _ _ z q (point_ι τ hτ _ z hz)).symm.trans
    (D.transition i j z hz.1 hz.2)
end PELOriginalProductLineScalarEvaluation318
