module
public import PELOriginalAlgebraicSectionRecovery318
public import ReducedSchemeGlobalFunctionSeparation318
public import PELOriginalWholePowerSectionField318
public section
noncomputable section
namespace PELOriginalWholeCubicRegularCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartSchemePointIdentity318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalSectionMultiplication318
open PELOriginalWholeCubicFrames318 PELOriginalWholeCubicCoefficientEvaluation318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- The literal whole affine coefficient equivalence, with both the
open-ring identification and the original chart isomorphism retained. -/
@[expose] def coefficientEquiv (j : Label 3) :
    Γ(candidate τ hτ,candidateChart τ hτ j) ≃+* CoordinateChart τ hτ j :=
  ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).symm ≪≫
    Scheme.Γ.mapIso (actualChartIso τ hτ j).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).commRingCatIsoToRingEquiv

lemma coefficient_evaluation (j : Label 3) (c : Γ(candidate τ hτ,candidateChart τ hτ j))
    (z : ComplexVectors) (hz : value τ hτ 3 j z≠0)
    (p : Spec (CommRingCat.of ℂ) ⟶ (candidateChart τ hτ j).toScheme)
    (hp : p≫(candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv c))=
      algebraEvaluation τ hτ z j hz (coefficientEquiv τ hτ j c) := by
  have he : p=Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      (actualChartIso τ hτ j).hom := by
    apply (cancel_mono (candidateChart τ hτ j).ι).1
    rw [Category.assoc]
    exact hp.trans (chart_point τ hτ j z hz).symm
  rw [he]
  let u := (actualChartIso τ hτ j).hom.appTop
    ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv c)
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)).appTop u)=
    algebraEvaluation τ hτ z j hz ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom u)
  have hc := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom))
    ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom u)
  rw [Iso.hom_inv_id_apply] at hc
  rw [←hc]
  exact Iso.inv_hom_id_apply _ _

lemma point_nonzero (j : Label 3) (z : ComplexVectors)
    (p : Spec (CommRingCat.of ℂ) ⟶ (candidateChart τ hτ j).toScheme)
    (hp : p≫(candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    value τ hτ 3 j z≠0 := by
  apply ProjectivePreimageRegularRatios318.point_coordinate_nonzero (inclusion τ hτ) j p
    (fun i => value τ hτ 3 i z) (cover_nonzero τ hτ z)
  rw [←Category.assoc,hp,candidateComplexPoint_inclusion]
  exact (PELOriginalMixedPointEvaluation318.cubic_covering_point τ hτ z).symm

@[expose] def regularCoefficient (m : ℕ) (s : homogeneous τ hτ (3*m)) (j : Label 3) :
    Γ(candidate τ hτ,candidateChart τ hτ j) :=
  (coefficientEquiv τ hτ j).symm (PELOriginalWholePowerRegularization318.linear τ hτ m j s)

/-- Every original full section supplies compatible regular coefficients
on the NINE WHOLE cubic charts, not just the mixed refinement. -/
theorem transition (m : ℕ) (s : homogeneous τ hτ (3*m)) (j k : Label 3) :
    (candidate τ hτ).presheaf.map (homOfLE inf_le_left).op (regularCoefficient τ hτ m s j)=
      ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
        (frame τ hτ)).transition j k).val^m *
      (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op (regularCoefficient τ hτ m s k) := by
  let W := candidateChart τ hτ j ⊓ candidateChart τ hτ k
  let π := W.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  apply (LineFrameTopScalar318.ringTop W).inv.injective
  apply ReducedSchemeGlobalFunctionSeparation318.ext π
  intro p hp
  obtain ⟨l,z,hl,hz⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ
    (p≫W.ι) hp
  have hpz : p≫W.ι=candidateComplexPoint τ hτ (projection (P τ) z) :=
    hz.trans (chart_point τ hτ l z hl)
  let pL := p≫(candidate τ hτ).homOfLE (show W ≤ candidateChart τ hτ j from inf_le_left)
  let pR := p≫(candidate τ hτ).homOfLE (show W ≤ candidateChart τ hτ k from inf_le_right)
  have hL : pL≫(candidateChart τ hτ j).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [pL,Category.assoc,Scheme.homOfLE_ι] using hpz
  have hR : pR≫(candidateChart τ hτ k).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [pR,Category.assoc,Scheme.homOfLE_ι] using hpz
  have hj := point_nonzero τ hτ j z pL hL
  have hk := point_nonzero τ hτ k z pR hR
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  simp only [map_mul,map_pow]
  rw [restriction_pullback,restriction_pullback]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (pL.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv (regularCoefficient τ hτ m s j)))=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop W).inv
        ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
          (frame τ hτ)).transition j k).val)))^m *
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (pR.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ k)).inv (regularCoefficient τ hτ m s k)))
  rw [coefficient_evaluation τ hτ j _ z hj pL hL,
    coefficient_evaluation τ hτ k _ z hk pR hR,transition_evaluation τ hτ j k z hj hk p hpz]
  simp only [regularCoefficient,RingEquiv.apply_symm_apply,
    PELOriginalWholePowerRegularization318.cover_evaluation,
    PELOriginalWholePowerRatioCover318.coverRatio]
  field_simp [hj,hk]
end PELOriginalWholeCubicRegularCoefficients318
