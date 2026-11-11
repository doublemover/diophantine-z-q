module
public import PELOriginalWholeCubicFrames318
public import PELOriginalCompatibleRegularSection318
public import PELOriginalMixedPointEvaluation318
public section
noncomputable section
namespace PELOriginalWholeCubicCoefficientEvaluation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartSchemePointIdentity318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalWholeCubicFrames318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalPolarizationTransitions318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma element_evaluation (m : ℕ)
    (s : Γ(FramedLineTensorPower318.object (cubicSheaf τ hτ) m,⊤))
    (j : Label 3) (z : ComplexVectors) (hz : value τ hτ 3 j z≠0)
    (p : Spec (CommRingCat.of ℂ) ⟶ (candidateChart τ hτ j).toScheme)
    (hp : p≫(candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv (coefficient τ hτ m s j)))=
    algebraEvaluation τ hτ z j hz (element τ hτ m s j) := by
  have he : p=Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      (actualChartIso τ hτ j).hom := by
    apply (cancel_mono (candidateChart τ hτ j).ι).1
    rw [Category.assoc]
    exact hp.trans (chart_point τ hτ j z hz).symm
  rw [he]
  let u := (actualChartIso τ hτ j).hom.appTop
    ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv (coefficient τ hτ m s j))
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)).appTop u)=
    algebraEvaluation τ hτ z j hz ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom u)
  have hc := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom))
    ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom u)
  rw [Iso.hom_inv_id_apply] at hc
  rw [←hc]
  exact Iso.inv_hom_id_apply _ _

/-- Any original representative lying in two cubic charts has a genuine
scheme-valued lift into their WHOLE actual open intersection. -/
lemma overlap_point (j k : Label 3) (z : ComplexVectors)
    (hj : value τ hτ 3 j z≠0) (hk : value τ hτ 3 k z≠0) :
    ∃ p : Spec (CommRingCat.of ℂ) ⟶ (candidateChart τ hτ j ⊓ candidateChart τ hτ k).toScheme,
      p≫(candidateChart τ hτ j ⊓ candidateChart τ hτ k).ι=
        candidateComplexPoint τ hτ (projection (P τ) z) := by
  let f := candidateComplexPoint τ hτ (projection (P τ) z)
  have hm (i : Label 3) (hi : value τ hτ 3 i z≠0) (x : Spec (CommRingCat.of ℂ)) :
      f x∈candidateChart τ hτ i := by
    rw [f,←chart_point τ hτ i z hi]
    exact ((actualChartIso τ hτ i).hom
      (Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z i hi).toRingHom) x)).property
  have hr : Set.range f ⊆ Set.range (candidateChart τ hτ j ⊓ candidateChart τ hτ k).ι := by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨f x,hm j hj x,hm k hk x⟩,rfl⟩
  exact ⟨IsOpenImmersion.lift _ f hr,IsOpenImmersion.lift_fac _ _ hr⟩

lemma restriction_pullback {X : Scheme} (U W : X.Opens) (h : W ≤ U) (c : Γ(X,U)) :
    (LineFrameTopScalar318.ringTop W).inv (X.presheaf.map (homOfLE h).op c)=
      (X.homOfLE h).appTop ((LineFrameTopScalar318.ringTop U).inv c) := by
  have he := OriginalOpenCoefficientSpecialization318.coefficient_pullback U W h
    ((LineFrameTopScalar318.ringTop U).inv c)
  simpa only [GlobalSectionFrameCoordinates318.coefficient,Iso.inv_hom_id_apply] using he

/-- Actual whole-ring cubic transition specialized through a genuine
point of the overlap, retaining the original cubic coordinate ratio. -/
lemma transition_evaluation (j k : Label 3) (z : ComplexVectors)
    (hj : value τ hτ 3 j z≠0) (hk : value τ hτ 3 k z≠0)
    (p : Spec (CommRingCat.of ℂ) ⟶ (candidateChart τ hτ j ⊓ candidateChart τ hτ k).toScheme)
    (hp : p≫(candidateChart τ hτ j ⊓ candidateChart τ hτ k).ι=
      candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j ⊓ candidateChart τ hτ k)).inv
        ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
          (frame τ hτ)).transition j k).val))=value τ hτ 3 k z/value τ hτ 3 j z := by
  rw [transition_value,OriginalOpenCoefficientSpecialization318.coefficient_pullback]
  let q := p≫(candidate τ hτ).homOfLE
    (show candidateChart τ hτ j ⊓ candidateChart τ hτ k ≤ candidateChart τ hτ j from inf_le_left)
  have hq : q≫(candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι] using hp
  have hbase : q≫(candidateChart τ hτ j).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hq]
    exact PELOriginalProperComplexCandidate318.candidate_point_over τ hτ _
  have hpoint : q≫(candidateChart τ hτ j).ι≫inclusion τ hτ=
      ComplexProjectiveSchemePoint318.point (fun i => value τ hτ 3 i z) (cover_nonzero τ hτ z) := by
    rw [←Category.assoc,hq,candidateComplexPoint_inclusion]
    exact (PELOriginalMixedPointEvaluation318.cubic_covering_point τ hτ z).symm
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((q≫(candidate τ hτ).homOfLE (show candidateChart τ hτ j ≤ candidateChart τ hτ j from le_rfl)).appTop
      (ProjectivePreimageRegularRatios318.ratioSection (inclusion τ hτ) j k))=_
  have hid : (candidate τ hτ).homOfLE (show candidateChart τ hτ j ≤ candidateChart τ hτ j from le_rfl)=𝟙 _ := by
    apply (cancel_mono (candidateChart τ hτ j).ι).1
    simp only [Scheme.homOfLE_ι,Category.id_comp]
  rw [hid,Category.comp_id]
  exact ProjectivePreimageRegularRatios318.evaluation (inclusion τ hτ)
    (PELOriginalProperComplexCandidate318.structureMap τ hτ)
    (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) j k q hbase _
    (cover_nonzero τ hτ z) hj hpoint
end PELOriginalWholeCubicCoefficientEvaluation318
