module
public import PELOriginalOrderSchemeMorphism318
public import QuaternionicOrderQuotientActionLaws318
public import PELOriginalIntegerEndomorphismLaws318
public section
noncomputable section
namespace PELOriginalOrderSchemeLaws318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalOrderSchemeMorphism318 PELPrincipalOrderCoordinates318
open PELQuaternionRealRepresentation318 QuaternionicOrderPeriodQuotient318
open QuaternionicOrderQuotientActionLaws318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma morphism_zero : morphism τ hτ 0=constantZero τ hτ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ 0) (constantZero_over τ hτ)
  intro q
  rw [point_action,zero_action,constantZero_action]
  rfl
lemma morphism_one : morphism τ hτ 1=𝟙 _ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ 1) (Category.id_comp _)
  intro q
  rw [point_action,one_action,Category.comp_id]

/-- Addition in the FULL original order becomes the actual regular
pointwise sum of the independently constructed scheme maps. -/
theorem morphism_add (a b : order) :
    morphism τ hτ (a+b)=combine τ hτ (morphism τ hτ a) (morphism τ hτ b)
      ((over_complex τ hτ a).trans (over_complex τ hτ b).symm) := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ (a+b))
    ((combine_over τ hτ _ _ _).trans (over_complex τ hτ a))
  intro q
  rw [point_action,combine_action τ hτ _ _ _ _
    (orderEnd representation order τ a q) (orderEnd representation order τ b q)
    (point_action τ hτ a q) (point_action τ hτ b q),add_action]

/-- Multiplication is represented in its correct NONCOMMUTATIVE order:
categorical composition a then b represents b*a. -/
theorem morphism_comp (a b : order) :
    morphism τ hτ a≫morphism τ hτ b=morphism τ hτ (b*a) := by
  apply unary_ext τ hτ _ _ (by rw [Category.assoc,over_complex,over_complex])
    (over_complex τ hτ (b*a))
  intro q
  rw [←Category.assoc,point_action,point_action,point_action,mul_action]

/-- Every actual order map is an algebraic GROUP endomorphism: this is
an equality on the whole scheme product, not only the original torus. -/
theorem morphism_addition (a : order) :
    PELOriginalAdditionSchemeMorphism318.addition τ hτ≫morphism τ hτ a=
      combine τ hτ (pullback.fst (π τ hτ) (π τ hτ)≫morphism τ hτ a)
        (pullback.snd (π τ hτ) (π τ hτ)≫morphism τ hτ a)
        (by simp only [Category.assoc,over_complex]; exact pullback.condition) := by
  apply PELOriginalProductComplexPoints318.morphism_ext τ hτ
  · rw [Category.assoc,over_complex]
    exact PELOriginalAdditionSchemeMorphism318.over_complex τ hτ
  · rw [combine_over,Category.assoc,over_complex]
    rfl
  intro z w
  have hf := pair_fst_assoc τ hτ (DiscreteComplexPeriodAtlas318.projection (P τ) z)
    (DiscreteComplexPeriodAtlas318.projection (P τ) w) (morphism τ hτ a)
  have hg := pair_snd_assoc τ hτ (DiscreteComplexPeriodAtlas318.projection (P τ) z)
    (DiscreteComplexPeriodAtlas318.projection (P τ) w) (morphism τ hτ a)
  rw [point_action] at hf hg
  rw [←Category.assoc,PELOriginalAdditionSchemeMorphism318.pair_action,point_action,
    combine_action τ hτ _ _ _ _ _ _ hf hg,map_add]

lemma morphism_zeroPoint (a : order) : zeroPoint τ hτ≫morphism τ hτ a=zeroPoint τ hτ := by
  change candidateComplexPoint τ hτ 0≫morphism τ hτ a=candidateComplexPoint τ hτ 0
  rw [point_action,map_zero]
end PELOriginalOrderSchemeLaws318
