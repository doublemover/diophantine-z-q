module
public import PELOriginalTripleProductReduced318
public section
noncomputable section
namespace PELOriginalTripleComplexPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalCandidateComplexPoints318 PELOriginalProductChartCover318
open PELOriginalProductComplexPoints318 PELOriginalTripleProductReduced318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def structureMap : Triple τ hτ ⟶ Spec (CommRingCat.of ℂ) :=
  pullback.fst (baseMap τ hτ) (π τ hτ)≫baseMap τ hτ

instance tripleFiniteType : LocallyOfFiniteType (structureMap τ hτ) := by
  dsimp [structureMap]
  infer_instance

@[expose] def triple (q r s : Base τ) : Spec (CommRingCat.of ℂ) ⟶ Triple τ hτ :=
  pullback.lift (pair τ hτ q r) (candidateComplexPoint τ hτ s)
    ((pair_over τ hτ q r).trans
      (PELOriginalProperComplexCandidate318.candidate_point_over τ hτ s).symm)

@[reassoc] lemma triple_fst (q r s : Base τ) :
    triple τ hτ q r s≫pullback.fst _ _=pair τ hτ q r := pullback.lift_fst _ _ _
@[reassoc] lemma triple_snd (q r s : Base τ) :
    triple τ hτ q r s≫pullback.snd _ _=candidateComplexPoint τ hτ s := pullback.lift_snd _ _ _
@[reassoc] lemma triple_over (q r s : Base τ) : triple τ hτ q r s≫structureMap τ hτ=𝟙 _ := by
  rw [structureMap,←Category.assoc,triple_fst,pair_over]

/-- ALL over-C morphisms to the actual triple product come from three
original torus points, as literal scheme-morphism equality. -/
theorem every_point (p : Spec (CommRingCat.of ℂ) ⟶ Triple τ hτ)
    (hp : p≫structureMap τ hτ=𝟙 _) :
    ∃ z a b : ComplexVectors, p=triple τ hτ (projection (P τ) z)
      (projection (P τ) a) (projection (P τ) b) := by
  have hleft : (p≫pullback.fst (baseMap τ hτ) (π τ hτ))≫baseMap τ hτ=𝟙 _ := by
    simpa only [structureMap,Category.assoc] using hp
  have hright : (p≫pullback.snd (baseMap τ hτ) (π τ hτ))≫π τ hτ=𝟙 _ := by
    rw [Category.assoc,←pullback.condition]
    exact hp
  obtain ⟨z,a,hza⟩ := PELOriginalProductComplexPoints318.every_point τ hτ _ hleft
  obtain ⟨j,b,hb,hbe⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ _ hright
  refine ⟨z,a,b,?_⟩
  apply pullback.hom_ext
  · rw [triple_fst,hza]
  · rw [triple_snd,hbe,PELOriginalChartSchemePointIdentity318.chart_point]

/-- The exact reduced finite-type/separated comparison interface for
whole candidate-valued maps on triples. -/
theorem morphism_ext
    (f g : Triple τ hτ ⟶ PELOriginalReducedProjectiveCandidate318.candidate τ hτ)
    (hf : f≫π τ hτ=structureMap τ hτ) (hg : g≫π τ hτ=structureMap τ hτ)
    (h : ∀ z a b : ComplexVectors,
      triple τ hτ (projection (P τ) z) (projection (P τ) a) (projection (P τ) b)≫f=
        triple τ hτ (projection (P τ) z) (projection (P τ) a) (projection (P τ) b)≫g) : f=g := by
  apply ReducedComplexPointMorphisms318.ext (structureMap τ hτ) (π τ hτ) f g hf hg
  intro p hp
  obtain ⟨z,a,b,rfl⟩ := every_point τ hτ p hp
  exact h z a b
end PELOriginalTripleComplexPoints318
