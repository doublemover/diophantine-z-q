module
public import PELOriginalNegationLineGauge318
public import PELOriginalOpenFunctionSeparation318
public section
noncomputable section
namespace PELOriginalNegationLineCocycle318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalNegationLineCover318
open PELOriginalNegationLineGauge318 PELOriginalOpenRegularFunction318
open PELOriginalOpenRegularNaturality318 PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev sourceCocycle := LineFrameCocycle318.cocycle (sheaf τ hτ) (chart τ hτ) (sourceFrame τ hτ)
abbrev targetCocycle := LineFrameCocycle318.cocycle (pullback τ hτ) (chart τ hτ) (targetFrame τ hτ)

lemma source_transition (a b : PELOriginalNegationLineCover318.Index τ hτ) :
    (sourceCocycle τ hτ).transition a b=
      Units.map ((candidate τ hτ).presheaf.map (homOfLE
        (show chart τ hτ a ⊓ chart τ hτ b ≤ opens τ hτ a.1 ⊓ opens τ hτ b.1 from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).op).hom.toMonoidHom
        ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a.1 b.1) := by
  change FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame _ _ (sourceFrame τ hτ a) _ inf_le_left)
    (OpenLineFrameCoordinates318.frame _ _ (sourceFrame τ hτ b) _ inf_le_right)=_
  simp only [sourceFrame,OpenLineFrameRefinement318.coordinates]
  exact (LineFrameTransitions318.restrict (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame
    a.1 b.1 inf_le_left inf_le_right _).symm

lemma target_transition (a b : PELOriginalNegationLineCover318.Index τ hτ) :
    (targetCocycle τ hτ).transition a b=
      Units.map ((candidate τ hτ).presheaf.map (homOfLE
        (show chart τ hτ a ⊓ chart τ hτ b ≤ negative τ hτ ⁻¹ᵁ (opens τ hτ a.2 ⊓ opens τ hτ b.2) from
          fun x hx => ⟨hx.1.2,hx.2.2⟩)).op).hom.toMonoidHom
        (Units.map ((negative τ hτ).app (opens τ hτ a.2 ⊓ opens τ hτ b.2)).hom.toMonoidHom
          ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a.2 b.2)) := by
  change FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame _ _ (targetFrame τ hτ a) _ inf_le_left)
    (OpenLineFrameCoordinates318.frame _ _ (targetFrame τ hτ b) _ inf_le_right)=_
  simp only [targetFrame,OpenLineFrameRefinement318.coordinates]
  exact TranslatedLineIsoScalars318.target_transition_subopen (negative τ hτ) (sheaf τ hτ)
    (opens τ hτ) (line τ hτ).frame a.2 b.2 _ _

/-- The produced regular unit gauge identifies the WHOLE extracted
cocycles of the actual inverse pullback and the original degree-one line.
Original point calculations are upgraded by reduced-scheme separation. -/
theorem gauge_equation (a b : PELOriginalNegationLineCover318.Index τ hτ) :
    (sourceCocycle τ hτ).transition a b=
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (candidate τ hτ)).obj
        (chart τ hτ) (gauge τ hτ) a b * (targetCocycle τ hτ).transition a b := by
  let W := chart τ hτ a ⊓ chart τ hτ b
  apply PELOriginalOpenFunctionSeparation318.unit_ext τ hτ W
  intro z hz
  have ha := (domain_iff τ hτ a z).mp hz.1
  have hb := (domain_iff τ hτ b z).mp hz.2
  rw [source_transition,target_transition]
  simp only [UnitTransitionCocycle318.coboundary,Units.val_mul,Units.coe_map]
  rw [value_eq_evaluation τ hτ W _ z hz,value_eq_evaluation τ hτ W _ z hz]
  change (evaluation τ hτ W z hz) (_)=_
  simp only [map_mul]
  have hs := value_restrict τ hτ (opens τ hτ a.1 ⊓ opens τ hτ b.1) W
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a.1 b.1).val z hz
  have ht := value_restrict τ hτ (negative τ hτ ⁻¹ᵁ (opens τ hτ a.2 ⊓ opens τ hτ b.2)) W
    (fun x hx => ⟨hx.1.2,hx.2.2⟩)
    ((negative τ hτ).app (opens τ hτ a.2 ⊓ opens τ hτ b.2)
      ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame).transition a.2 b.2).val) z hz
  have hneg : z∈domain τ hτ (negative τ hτ ⁻¹ᵁ (opens τ hτ a.2 ⊓ opens τ hτ b.2)) :=
    ⟨hz.1.2,hz.2.2⟩
  rw [value_pullback τ hτ (negative τ hτ) (fun w => -w) (negative_point τ hτ)
    (opens τ hτ a.2 ⊓ opens τ hτ b.2) _ z hneg] at ht
  have hga := value_restrict τ hτ (chart τ hτ a) W inf_le_left (gauge τ hτ a).val z hz
  have hgb := value_restrict τ hτ (chart τ hτ b) W inf_le_right (gauge τ hτ b).val z hz
  rw [PELOriginalTranslationFrameValues318.transition_value τ hτ a.1 b.1 z ha.1 hb.1] at hs
  rw [PELOriginalTranslationFrameValues318.transition_value τ hτ a.2 b.2 (-z) ha.2 hb.2] at ht
  rw [gauge_value τ hτ a z hz.1] at hga
  rw [gauge_value τ hτ b z hz.2] at hgb
  simp only [value_eq_evaluation τ hτ W _ z hz] at hs ht hga hgb
  have hinv (u : Γ(candidate τ hτ,W)ˣ) :
      evaluation τ hτ W z hz (u⁻¹).val=(evaluation τ hτ W z hz u.val)⁻¹ := by
    change (Units.map (evaluation τ hτ W z hz).toMonoidHom (u⁻¹)).val=_
    rw [map_inv,Units.val_inv_eq_inv_val,Units.coe_map]
  rw [hinv,hs,ht,hga,hgb]
  have h1 := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.1.val z
    (theta_nonzero τ hτ a.1 z ha.1)
  have h2 := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.2.val (-z)
    (theta_nonzero τ hτ a.2 (-z) ha.2)
  have h3 := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ b.1.val z
    (theta_nonzero τ hτ b.1 z hb.1)
  have h4 := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ b.2.val (-z)
    (theta_nonzero τ hτ b.2 (-z) hb.2)
  dsimp only [chartGauge] at *
  field_simp [h1,h2,h3,h4]
end PELOriginalNegationLineCocycle318
