module
public import PELOriginalUniversalOrderAction318
public import PELOriginalTranslationAutomorphisms318
public section
noncomputable section
namespace PELOriginalOrderAutomorphisms318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalOrderSchemeMorphism318
open PELOriginalOrderSchemeLaws318 PELPrincipalOrderCoordinates318
open PELQuaternionRealRepresentation318 QuaternionicOrderPeriodQuotient318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Every unit of the ORIGINAL order induces a genuine algebraic
automorphism, whose inverse is the original inverse order element. -/
@[expose] def unitIso (u : orderˣ) : candidate τ hτ ≅ candidate τ hτ where
  hom := morphism τ hτ u.val
  inv := morphism τ hτ (↑(u⁻¹) : order)
  hom_inv_id := by rw [morphism_comp,Units.inv_mul,morphism_one]
  inv_hom_id := by rw [morphism_comp,Units.mul_inv,morphism_one]

/-- The actual algebraic action intertwines genuine translations,
retaining the literal original order action on the translating point. -/
theorem translation_square (a : order) (q : Base τ) :
    PELOriginalTranslationAutomorphisms318.translation τ hτ q≫morphism τ hτ a=
      morphism τ hτ a≫PELOriginalTranslationAutomorphisms318.translation τ hτ
        (orderEnd representation order τ a q) := by
  apply unary_ext τ hτ
  · rw [Category.assoc,over_complex,PELOriginalTranslationAutomorphisms318.over_complex]
  · rw [Category.assoc,PELOriginalTranslationAutomorphisms318.over_complex,over_complex]
  intro r
  rw [←Category.assoc,PELOriginalTranslationAutomorphisms318.original_action,point_action,
    ←Category.assoc,point_action,PELOriginalTranslationAutomorphisms318.original_action,map_add]

/-- On genuine complex points, the represented ring action is EXACTLY
the original quaternionic action through the already-proved additive
theta equivalence. Algebraicity was constructed before this comparison. -/
theorem original_equiv_action (a : order) (q : Base τ) :
    PELOriginalUniversalOrderAction318.endomorphism τ hτ (𝟙 (Spec (CommRingCat.of ℂ))) a
      (PELOriginalTorusPointAddEquiv318.originalAddEquiv τ hτ q)=
    PELOriginalTorusPointAddEquiv318.originalAddEquiv τ hτ
      (orderEnd representation order τ a q) := by
  apply Subtype.ext
  exact point_action τ hτ a q
end PELOriginalOrderAutomorphisms318
