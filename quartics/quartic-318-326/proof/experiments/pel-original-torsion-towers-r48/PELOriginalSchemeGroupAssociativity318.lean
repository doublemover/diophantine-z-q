module
public import PELOriginalSchemeGroupUnitInverse318
public section
noncomputable section
namespace PELOriginalSchemeGroupAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318
open PELOriginalAdditionSchemeMorphism318 PELOriginalSchemeAdditionOperations318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The three literal projections of (X times_C X) times_C X. -/
@[expose] def first : Triple τ hτ ⟶ candidate τ hτ :=
  pullback.fst (baseMap τ hτ) (π τ hτ)≫pullback.fst (π τ hτ) (π τ hτ)
@[expose] def second : Triple τ hτ ⟶ candidate τ hτ :=
  pullback.fst (baseMap τ hτ) (π τ hτ)≫pullback.snd (π τ hτ) (π τ hτ)
@[expose] def third : Triple τ hτ ⟶ candidate τ hτ :=
  pullback.snd (baseMap τ hτ) (π τ hτ)

@[reassoc] lemma first_over : first τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [first,Category.assoc]
  rfl
@[reassoc] lemma second_over : second τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [second,Category.assoc,←pullback.condition]
  rfl
@[reassoc] lemma third_over : third τ hτ≫π τ hτ=structureMap τ hτ := by
  exact (pullback.condition (f := baseMap τ hτ) (g := π τ hτ)).symm

lemma first_action (q r s : Base τ) :
    triple τ hτ q r s≫first τ hτ=candidateComplexPoint τ hτ q := by
  rw [first,←Category.assoc,triple_fst,pair_fst]
lemma second_action (q r s : Base τ) :
    triple τ hτ q r s≫second τ hτ=candidateComplexPoint τ hτ r := by
  rw [second,←Category.assoc,triple_fst,pair_snd]
lemma third_action (q r s : Base τ) :
    triple τ hτ q r s≫third τ hτ=candidateComplexPoint τ hτ s := triple_snd τ hτ q r s

@[expose] def firstTwo : Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (first τ hτ) (second τ hτ)
    ((first_over τ hτ).trans (second_over τ hτ).symm)
@[expose] def lastTwo : Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (second τ hτ) (third τ hτ)
    ((second_over τ hτ).trans (third_over τ hτ).symm)
@[reassoc] lemma firstTwo_over : firstTwo τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [firstTwo,combine_over,first_over]
@[reassoc] lemma lastTwo_over : lastTwo τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [lastTwo,combine_over,second_over]
lemma firstTwo_action (q r s : Base τ) :
    triple τ hτ q r s≫firstTwo τ hτ=candidateComplexPoint τ hτ (q+r) :=
  combine_action τ hτ _ _ _ _ q r (first_action τ hτ q r s) (second_action τ hτ q r s)
lemma lastTwo_action (q r s : Base τ) :
    triple τ hτ q r s≫lastTwo τ hτ=candidateComplexPoint τ hτ (r+s) :=
  combine_action τ hτ _ _ _ _ r s (second_action τ hτ q r s) (third_action τ hτ q r s)

/-- The two actual regular triple composites, with all base squares
proved from the genuine product maps. -/
@[expose] def leftAssociated : Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (firstTwo τ hτ) (third τ hτ)
    ((firstTwo_over τ hτ).trans (third_over τ hτ).symm)
@[expose] def rightAssociated : Triple τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (first τ hτ) (lastTwo τ hτ)
    ((first_over τ hτ).trans (lastTwo_over τ hτ).symm)
@[reassoc] lemma leftAssociated_over : leftAssociated τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [leftAssociated,combine_over,firstTwo_over]
@[reassoc] lemma rightAssociated_over : rightAssociated τ hτ≫π τ hτ=structureMap τ hτ := by
  rw [rightAssociated,combine_over,first_over]
lemma leftAssociated_action (q r s : Base τ) :
    triple τ hτ q r s≫leftAssociated τ hτ=candidateComplexPoint τ hτ ((q+r)+s) :=
  combine_action τ hτ _ _ _ _ (q+r) s (firstTwo_action τ hτ q r s) (third_action τ hτ q r s)
lemma rightAssociated_action (q r s : Base τ) :
    triple τ hτ q r s≫rightAssociated τ hτ=candidateComplexPoint τ hτ (q+(r+s)) :=
  combine_action τ hτ _ _ _ _ q (r+s) (first_action τ hτ q r s) (lastTwo_action τ hτ q r s)

/-- Associativity as equality of genuine scheme morphisms on the whole
729-chart triple product. The actual reduced triple source, full C-point
realization and separated target upgrade the original torus identity;
there is no pointwise-only group structure or transported regularity. -/
theorem associative : leftAssociated τ hτ=rightAssociated τ hτ := by
  apply PELOriginalTripleComplexPoints318.morphism_ext τ hτ _ _
    (leftAssociated_over τ hτ) (rightAssociated_over τ hτ)
  intro z a b
  rw [leftAssociated_action,rightAssociated_action,add_assoc]
end PELOriginalSchemeGroupAssociativity318
