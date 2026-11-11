module
public import PELOriginalSchemeAdditionOperations318
public section
noncomputable section
namespace PELOriginalSchemeGroupUnitInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalAdditionSchemeMorphism318 PELOriginalSchemeAdditionOperations318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def constantZero : candidate τ hτ ⟶ candidate τ hτ := π τ hτ≫zeroPoint τ hτ
@[reassoc] lemma constantZero_over : constantZero τ hτ≫π τ hτ=π τ hτ := by
  rw [constantZero,Category.assoc,zero_over,Category.comp_id]
lemma constantZero_action (q : Base τ) :
    candidateComplexPoint τ hτ q≫constantZero τ hτ=zeroPoint τ hτ := by
  rw [constantZero,←Category.assoc,PELOriginalProperComplexCandidate318.candidate_point_over,
    Category.id_comp]

/-- Left and right unit laws are full scheme-morphism equalities on the
entire candidate, including every prime and its structure sheaf. -/
theorem left_unit :
    combine τ hτ (constantZero τ hτ) (𝟙 _)
      ((constantZero_over τ hτ).trans (Category.id_comp _).symm)=𝟙 _ := by
  apply unary_ext τ hτ
  · rw [combine_over,constantZero_over]
  · exact Category.id_comp _
  intro q
  rw [combine_action τ hτ _ _ _ _ 0 q (constantZero_action τ hτ q) (Category.comp_id _),
    zero_add,Category.comp_id]

theorem right_unit :
    combine τ hτ (𝟙 _) (constantZero τ hτ)
      ((Category.id_comp _).trans (constantZero_over τ hτ).symm)=𝟙 _ := by
  apply unary_ext τ hτ
  · rw [combine_over,Category.id_comp]
  · exact Category.id_comp _
  intro q
  rw [combine_action τ hτ _ _ _ _ q 0 (Category.comp_id _) (constantZero_action τ hτ q),
    add_zero,Category.comp_id]

/-- The actual projective negation is the inverse for the independently
constructed algebraic addition, on the whole candidate scheme. -/
theorem right_inverse :
    combine τ hτ (𝟙 _) (inverse τ hτ)
      ((Category.id_comp _).trans (inverse_over τ hτ).symm)=constantZero τ hτ := by
  apply unary_ext τ hτ
  · rw [combine_over,Category.id_comp]
  · exact constantZero_over τ hτ
  intro q
  simpa only [add_neg_cancel,constantZero_action,zeroPoint] using
    combine_action τ hτ _ _ _ _ q (-q) (Category.comp_id _) (inverse_action τ hτ q)

theorem left_inverse :
    combine τ hτ (inverse τ hτ) (𝟙 _)
      ((inverse_over τ hτ).trans (Category.id_comp _).symm)=constantZero τ hτ := by
  apply unary_ext τ hτ
  · rw [combine_over,inverse_over]
  · exact constantZero_over τ hτ
  intro q
  simpa only [neg_add_cancel,constantZero_action,zeroPoint] using
    combine_action τ hτ _ _ _ _ (-q) q (inverse_action τ hτ q) (Category.comp_id _)

/-- Commutativity on the actual whole fiber product over C. -/
theorem commutative :
    combine τ hτ (pullback.snd (π τ hτ) (π τ hτ))
      (pullback.fst (π τ hτ) (π τ hτ)) (pullback.condition.symm)=addition τ hτ := by
  apply PELOriginalProductComplexPoints318.morphism_ext τ hτ
  · rw [combine_over,←pullback.condition]
    rfl
  · exact over_complex τ hτ
  intro z a
  rw [combine_action τ hτ _ _ _ _ _ _ (pair_snd τ hτ _ _) (pair_fst τ hτ _ _),
    pair_action,add_comm]
end PELOriginalSchemeGroupUnitInverse318
