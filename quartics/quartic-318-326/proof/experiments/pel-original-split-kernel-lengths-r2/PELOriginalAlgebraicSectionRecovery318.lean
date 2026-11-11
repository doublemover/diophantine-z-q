module
public import PELOriginalWholeCubicCoefficientEvaluation318
public section
noncomputable section
namespace PELOriginalAlgebraicSectionRecovery318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalCandidateAffineCharts318 PELOriginalReducedProjectiveCandidate318
open PELOriginalCandidateComplexPoints318 PELOriginalChartAnalyticEvaluation318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalWholeCubicFrames318
open PELOriginalWholeCubicCoefficientEvaluation318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalPolarizationTransitions318
open PELOriginalSectionMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)
abbrev Power := FramedLineTensorPower318.object (cubicSheaf τ hτ) m

/-- The actual algebraic global section's full regular cocycle gives
compatibility of its WHOLE affine elements at all original cover points. -/
theorem compatible (s : Γ(Power τ hτ m,⊤)) (j k : Label 3) (z : ComplexVectors)
    (hj : value τ hτ 3 j z≠0) (hk : value τ hτ 3 k z≠0) :
    algebraEvaluation τ hτ z j hj (element τ hτ m s j)*(value τ hτ 3 j z)^m=
      algebraEvaluation τ hτ z k hk (element τ hτ m s k)*(value τ hτ 3 k z)^m := by
  obtain ⟨p,hp⟩ := overlap_point τ hτ j k z hj hk
  let W := candidateChart τ hτ j ⊓ candidateChart τ hτ k
  let ev : Γ(candidate τ hτ,W) →+* ℂ :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom).comp
      (LineFrameTopScalar318.ringTop W).inv.hom
  have he := congrArg ev (coefficient_transition τ hτ m s j k)
  simp only [map_mul,map_pow] at he
  have hjp : (p≫(candidate τ hτ).homOfLE (show W ≤ candidateChart τ hτ j from inf_le_left))≫
      (candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [Category.assoc,Scheme.homOfLE_ι] using hp
  have hkp : (p≫(candidate τ hτ).homOfLE (show W ≤ candidateChart τ hτ k from inf_le_right))≫
      (candidateChart τ hτ k).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [Category.assoc,Scheme.homOfLE_ι] using hp
  have hevj : ev ((candidate τ hτ).presheaf.map
      (homOfLE (show W ≤ candidateChart τ hτ j from inf_le_left)).op (coefficient τ hτ m s j))=
      algebraEvaluation τ hτ z j hj (element τ hτ m s j) := by
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop W).inv (_)))=_
    rw [restriction_pullback]
    exact element_evaluation τ hτ m s j z hj _ hjp
  have hevk : ev ((candidate τ hτ).presheaf.map
      (homOfLE (show W ≤ candidateChart τ hτ k from inf_le_right)).op (coefficient τ hτ m s k))=
      algebraEvaluation τ hτ z k hk (element τ hτ m s k) := by
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop W).inv (_)))=_
    rw [restriction_pullback]
    exact element_evaluation τ hτ m s k z hk _ hkp
  have hevt : ev ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
      (frame τ hτ)).transition j k).val=value τ hτ 3 k z/value τ hτ 3 j z :=
    transition_evaluation τ hτ j k z hj hk p hp
  rw [hevj,hevk,hevt] at he
  rw [he,div_pow]
  field_simp [hj]

@[expose] def data (s : Γ(Power τ hτ m,⊤)) :
    PELOriginalCompatibleRegularSection318.Data τ hτ m where
  element := element τ hτ m s
  compatible := compatible τ hτ m s

/-- EVERY actual algebraic global power section gives an original
holomorphic section. Local regularity and original automorphy are
proved, not built into the definition of the input algebraic section. -/
@[expose] def recover (s : Γ(Power τ hτ m,⊤)) : homogeneous τ hτ (3*m) :=
  PELOriginalCompatibleRegularSection318.recovered τ hτ m (data τ hτ m s)

theorem regularization_recover (s : Γ(Power τ hτ m,⊤)) (j : Label 3) :
    PELOriginalWholePowerRegularization318.linear τ hτ m j (recover τ hτ m s)=
      element τ hτ m s j :=
  PELOriginalCompatibleRegularSection318.regularization_recovered τ hτ m _ j

/-- Actual whole ring elements determine the algebraic global section.
Every restriction and inverse frame is used, so no fiberwise shortcut
or reducedness assumption on a sheaf is substituted for separation. -/
theorem elements_injective : Function.Injective (element τ hτ m) := by
  intro s t h
  have hc (j : Label 3) : coefficient τ hτ m s j=coefficient τ hτ m t j := by
    apply (LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv.injective
    apply (Scheme.Γ.mapIso (actualChartIso τ hτ j).op).hom.injective
    apply (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom.injective
    exact congrFun h j
  let localSections := fun j : Label 3 => (Power τ hτ m).presheaf.map
    (homOfLE (show candidateChart τ hτ j ≤ ⊤ from le_top)).op t
  have hcompat : TopCat.Presheaf.IsCompatible (Power τ hτ m).presheaf
      (candidateChart τ hτ) localSections := by
    intro j k
    have hj := congrArg (fun f => f t) ((Power τ hτ m).presheaf.map_comp
      (homOfLE (show candidateChart τ hτ j ≤ ⊤ from le_top)).op (homOfLE inf_le_left).op)
    have hk := congrArg (fun f => f t) ((Power τ hτ m).presheaf.map_comp
      (homOfLE (show candidateChart τ hτ k ≤ ⊤ from le_top)).op (homOfLE inf_le_right).op)
    exact hj.symm.trans hk
  obtain ⟨u,hu,hunique⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(Power τ hτ m).presheaf,(Power τ hτ m).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat (candidate τ hτ))
    (candidateChart τ hτ) ⊤ (fun _ => homOfLE le_top) (coversTop τ hτ) localSections hcompat
  have hs : s=u := hunique s (by
    intro j
    apply (OpenLineFrameCoordinates318.frame (Power τ hτ m) (candidateChart τ hτ j)
      (powerFrame τ hτ m j) (candidateChart τ hτ j) le_rfl).symm.injective
    exact hc j)
  exact hs.trans (hunique t (fun _ => rfl)).symm

theorem recover_injective : Function.Injective (recover τ hτ m) := by
  intro s t h
  apply elements_injective τ hτ m
  funext j
  rw [←regularization_recover,←regularization_recover,h]
end PELOriginalAlgebraicSectionRecovery318
