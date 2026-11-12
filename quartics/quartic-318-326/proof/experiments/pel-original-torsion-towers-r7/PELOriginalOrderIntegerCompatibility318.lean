module
public import PELOriginalOrderActionFaithful318
public section
noncomputable section
namespace PELOriginalOrderIntegerCompatibility318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open QuaternionicOrderPeriodQuotient318 QuaternionicOrderQuotientActionLaws318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemePointGroup318
open PELOriginalOrderSchemeMorphism318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma original_integer_action (n : ℤ) (q : PELOriginalPolarizationTransitions318.Base τ) :
    orderEnd representation order τ (n : order) q=n • q := by
  have he := map_zsmul (QuaternionicOrderQuotientActionLaws318.ringAction
    representation order τ).toAddMonoidHom (1 : order) n
  rw [zsmul_one,map_one] at he
  have hq := congrArg (fun f : AddMonoid.End (PeriodQuotient representation order τ) => f q) he
  exact hq

/-- The original central integers act by the SAME previously constructed
regular multiplication maps, with whole-scheme equality. -/
theorem integer_morphism (n : ℤ) : morphism τ hτ (n : order)=
    PELOriginalIntegerMultiplication318.multiplication τ hτ n := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ _) (PELOriginalIntegerMultiplication318.over_complex τ hτ n)
  intro q
  rw [point_action,original_integer_action,PELOriginalIntegerMultiplication318.original_action]

/-- Exact central integer action for arbitrary, possibly nonreduced,
scheme-valued points. -/
theorem integer_test_action (n : ℤ) {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (p : Points τ hτ Y ρ) :
    PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ (n : order) p=n • p := by
  apply Subtype.ext
  change p.val≫morphism τ hτ (n : order)=(n • p).val
  rw [integer_morphism]
  exact PELOriginalIntegerMultiplication318.test_action τ hτ n p.val p.property

/-- The order's minus one is the actual previously algebraized original
projective inversion, not merely an abstract inverse on point groups. -/
theorem negative_one_morphism : morphism τ hτ (-1 : order)=inverse τ hτ := by
  have he : ((-1 : ℤ) : order)=(-1 : order) := by simp only [Int.cast_neg,Int.cast_one]
  rw [←he,integer_morphism,PELOriginalIntegerEndomorphismLaws318.multiplication_neg_one]
end PELOriginalOrderIntegerCompatibility318
