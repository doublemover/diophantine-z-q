module
public import PELOriginalPolarizedOrderAction318
public import FieldLineClassTrivial318
public section
noncomputable section
namespace PELOriginalOrderAdjointUniqueness318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationBicharacter318
open PELOriginalTranslationLineClass318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalOrderHermitianAdjoint318
open QuaternionicOrderPeriodQuotient318 PELQuaternionRealRepresentation318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def universal : Points τ hτ (candidate τ hτ) (π τ hτ) := ⟨𝟙 _,Category.id_comp _⟩
@[expose] def constantPoint (q : Base τ) : Points τ hτ (candidate τ hτ) (π τ hτ) :=
  ⟨π τ hτ≫candidateComplexPoint τ hτ q,by
    rw [Category.assoc,PELOriginalProperComplexCandidate318.candidate_point_over,Category.comp_id]⟩
lemma constant_value (q : Base τ) : value τ hτ (π τ hτ) (constantPoint τ hτ q)=1 := by
  change LineClassPullbackHom318.pullback (π τ hτ≫candidateComplexPoint τ hτ q) (classOf (line τ hτ))=1
  rw [LineClassPullbackLaws318.pullback_composition,
    FieldLineClassTrivial318.class_eq_one ℂ,map_one]
lemma zero_value : value τ hτ (π τ hτ) (0 : Points τ hτ _ (π τ hτ))=1 := by
  exact constant_value τ hτ 0
/-- Restricting the actual normalized pairing to the universal point and
a constant original point recovers the honest translation-difference
class. Triviality of a field line is proved, not silently assumed. -/
lemma pairing_constant (q : Base τ) :
    pairing τ hτ (π τ hτ) (universal τ hτ) (constantPoint τ hτ q)=polarizationClass τ hτ q := by
  rw [pairing,constant_value,zero_value,inv_one,mul_one]
  change LineClassPullbackHom318.pullback (PELOriginalTranslationAutomorphisms318.translation τ hτ q)
      (classOf (line τ hτ)) *
    (LineClassPullbackHom318.pullback (𝟙 (candidate τ hτ)) (classOf (line τ hτ)))⁻¹=_
  rw [LineClassPullbackLaws318.pullback_identity]
  exact (class_formula τ hτ q).symm
lemma action_constant (a : order) (q : Base τ) :
    PELOriginalUniversalOrderAction318.endomorphism τ hτ (π τ hτ) a (constantPoint τ hτ q)=
      constantPoint τ hτ (orderEnd representation order τ a q) := by
  apply Subtype.ext
  change (π τ hτ≫candidateComplexPoint τ hτ q)≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a=_
  rw [Category.assoc,PELOriginalOrderSchemeMorphism318.point_action]
/-- The full actual line-valued pairing determines the adjoint uniquely
inside the faithful ORIGINAL order. Testing only Spec(C) would lose all
line classes; the proof instead tests the whole original candidate. -/
theorem unique (a b : order)
    (h : ∀ (T : Scheme) (ρ : T⟶Spec (CommRingCat.of ℂ)) (x y : Points τ hτ T ρ),
      pairing τ hτ ρ (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a x) y=
      pairing τ hτ ρ x (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ b y)) :
    b=adjoint a := by
  apply PELOriginalOrderActionFaithful318.original_action_injective τ hτ
  apply AddMonoidHom.ext
  intro q
  apply PELOriginalPolarizationClassFaithful318.polarization_class_injective τ hτ
  have he := h (candidate τ hτ) (π τ hτ) (universal τ hτ) (constantPoint τ hτ q)
  rw [PELOriginalRosatiTestPairing318.pairing_adjoint,action_constant,
    action_constant,pairing_constant,pairing_constant] at he
  exact he.symm
end PELOriginalOrderAdjointUniqueness318
