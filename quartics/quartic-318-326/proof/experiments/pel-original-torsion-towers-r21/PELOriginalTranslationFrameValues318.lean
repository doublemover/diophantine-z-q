module
public import TranslatedLineIsoScalars318
public import PELOriginalOpenRegularNaturality318
public import PELOriginalMixedTranslationGauge318
public import PELOriginalMixedPointEvaluation318
public import PELOriginalAlgebraicLineCocycle318
public import PELOriginalTranslationAutomorphisms318
public section
noncomputable section
namespace PELOriginalTranslationFrameValues318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalTranslationAutomorphisms318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Index := NonemptyIndex τ hτ
@[expose] def chartDomain (a : Index τ hτ) : Set ComplexVectors := domain τ hτ (opens τ hτ a)
@[expose] def chartGauge (a : Index τ hτ) : ComplexVectors → ℂ :=
  PELOriginalMixedTranslationGauge318.gauge τ hτ a.val
lemma theta_nonzero (a : Index τ hτ) (z : ComplexVectors) (hz : z∈chartDomain τ hτ a) :
    z∈PELOriginalMixedTranslationGauge318.domain τ hτ a.val :=
  PELOriginalMixedPointEvaluation318.coordinates_nonzero τ hτ a.val
    (point τ hτ (opens τ hτ a) z hz) z (point_ι τ hτ _ z hz)
lemma chart_cover (z : ComplexVectors) : ∃ a,z∈chartDomain τ hτ a :=
  nonempty_covers τ hτ (candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ))

lemma transition_value (a b : Index τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a) (hb : z∈chartDomain τ hτ b) :
    value τ hτ (opens τ hτ a ⊓ opens τ hτ b)
      ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a b).val z=
      chartGauge τ hτ b z/chartGauge τ hτ a z := by
  let W := opens τ hτ a ⊓ opens τ hτ b
  have hz : z∈domain τ hτ W := ⟨ha,hb⟩
  let p := point τ hτ W z hz
  have hp := point_ι τ hτ W z hz
  rw [value_at_point τ hτ W _ z p hp]
  change PELOriginalAlgebraicLineCocycle318.evaluation τ hτ a b p _=_
  rw [PELOriginalAlgebraicLineCocycle318.transition_evaluation]
  let q := p≫toLeft τ hτ a.val b.val
  have hq : q≫(opens τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [q,toLeft,Category.assoc,Scheme.homOfLE_ι] using hp
  have hqC : q≫(opens τ hτ a).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hq,PELOriginalProperComplexCandidate318.candidate_point_over]
  have hna := theta_nonzero τ hτ a z ha
  have hnb := theta_nonzero τ hτ b z hb
  rw [PELOriginalMixedPointEvaluation318.cubic_evaluation τ hτ a.val b.val.1 q hqC z hna.1 hq,
    PELOriginalMixedPointEvaluation318.quadratic_evaluation τ hτ a.val b.val.2 q hqC z hna.2 hq]
  dsimp only [chartGauge,PELOriginalMixedTranslationGauge318.gauge]
  field_simp [hna.1,hna.2,hnb.1,hnb.2]

variable (δ : ComplexVectors)
@[expose] def translate : candidate τ hτ ⟶ candidate τ hτ := translation τ hτ (projection (P τ) δ)
lemma translate_point (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z)≫translate τ hτ δ=
      candidateComplexPoint τ hτ (projection (P τ) (z+δ)) := by
  rw [translate,original_action,PELOriginalAdditionSchemeMorphism318.projection_add]

@[expose] def pairOpen (a : Index τ hτ × Index τ hτ) : (candidate τ hτ).Opens :=
  TranslatedLineIsoScalars318.domain (translate τ hτ δ) (opens τ hτ) a
lemma pair_domain (a : Index τ hτ × Index τ hτ) (z : ComplexVectors) :
    z∈domain τ hτ (pairOpen τ hτ δ a) ↔
      z∈chartDomain τ hτ a.1 ∧ z+δ∈chartDomain τ hτ a.2 := by
  change (_∈opens τ hτ a.1 ∧ translate τ hτ δ
      (candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ))∈opens τ hτ a.2) ↔ _
  rw [←Scheme.Hom.comp_apply,translate_point]
  rfl

variable (E : sheaf τ hτ ≅ (Scheme.Modules.pullback (translate τ hτ δ)).obj (sheaf τ hτ))
@[expose] def regularUnit (a : Index τ hτ × Index τ hτ) : Γ(candidate τ hτ,pairOpen τ hτ δ a)ˣ :=
  TranslatedLineIsoScalars318.unit (translate τ hτ δ) (sheaf τ hτ)
    (opens τ hτ) (line τ hτ).frame E a
@[expose] def coefficient (a : Index τ hτ × Index τ hτ) : ComplexVectors → ℂ :=
  value τ hτ (pairOpen τ hτ δ a) (regularUnit τ hτ δ E a).val
lemma coefficient_nonzero (a : Index τ hτ × Index τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a.1) (hb : z+δ∈chartDomain τ hτ a.2) :
    coefficient τ hτ δ E a z≠0 :=
  unit_value_ne_zero τ hτ _ _ z ((pair_domain τ hτ δ a z).mpr ⟨ha,hb⟩)
lemma coefficient_holomorphic (a : Index τ hτ × Index τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a.1) (hb : z+δ∈chartDomain τ hτ a.2) :
    DifferentiableAt ℂ (coefficient τ hτ δ E a) z :=
  differentiableAt_value τ hτ _ _ z ((pair_domain τ hτ δ a z).mpr ⟨ha,hb⟩)
lemma coefficient_periodic (a : Index τ hτ × Index τ hτ)
    (l : PELOriginalPolarizationAutomorphy318.L τ hτ) (z : ComplexVectors) :
    coefficient τ hτ δ E a (z+l.val)=coefficient τ hτ δ E a z := value_period τ hτ _ _ l z

lemma value_mul (U : (candidate τ hτ).Opens) (s t : Γ(candidate τ hτ,U))
    (z : ComplexVectors) (hz : z∈domain τ hτ U) :
    value τ hτ U (s*t) z=value τ hτ U s z*value τ hτ U t z := by
  rw [value_eq_evaluation τ hτ U _ z hz,value_eq_evaluation τ hτ U s z hz,
    value_eq_evaluation τ hτ U t z hz,map_mul]

/-- Specialization of the WHOLE regular-unit equation gives the exact
original gauge compatibility. Both source and translated target
cocycles are evaluated through actual Spec(C) morphisms. -/
lemma coefficient_compatibility (a b : Index τ hτ × Index τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a.1) (hat : z+δ∈chartDomain τ hτ a.2)
    (hb : z∈chartDomain τ hτ b.1) (hbt : z+δ∈chartDomain τ hτ b.2) :
    coefficient τ hτ δ E a z*(chartGauge τ hτ b.1 z/chartGauge τ hτ a.1 z)=
      (chartGauge τ hτ b.2 (z+δ)/chartGauge τ hτ a.2 (z+δ))*coefficient τ hτ δ E b z := by
  let W := pairOpen τ hτ δ a ⊓ pairOpen τ hτ δ b
  have hz : z∈domain τ hτ W :=
    ⟨(pair_domain τ hτ δ a z).mpr ⟨ha,hat⟩,(pair_domain τ hτ δ b z).mpr ⟨hb,hbt⟩⟩
  have hs : W ≤ opens τ hτ a.1 ⊓ opens τ hτ b.1 :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have ht : W ≤ translate τ hτ δ ⁻¹ᵁ (opens τ hτ a.2 ⊓ opens τ hτ b.2) := by
    intro x hx
    exact ⟨hx.1.2,hx.2.2⟩
  have hu := TranslatedLineIsoScalars318.overlap (translate τ hτ δ) (sheaf τ hτ)
    (opens τ hτ) (line τ hτ).frame E a b
  have he := congrArg (fun u : Γ(candidate τ hτ,W)ˣ => value τ hτ W u.val z) hu
  simp only [Units.val_mul,Units.coe_map] at he
  rw [value_mul τ hτ W _ _ z hz,value_mul τ hτ W _ _ z hz] at he
  rw [value_restrict τ hτ _ W inf_le_left _ z hz,
    value_restrict τ hτ _ W hs _ z hz,value_restrict τ hτ _ W ht _ z hz,
    value_restrict τ hτ _ W inf_le_right _ z hz] at he
  rw [value_pullback τ hτ (translate τ hτ δ) (fun w => w+δ) (translate_point τ hτ δ)
    (opens τ hτ a.2 ⊓ opens τ hτ b.2) _ z (ht hz),
    transition_value τ hτ a.1 b.1 z ha hb,transition_value τ hτ a.2 b.2 (z+δ) hat hbt] at he
  exact he
end PELOriginalTranslationFrameValues318
