module
public import PELOriginalAdditionSchemeMorphism318
public import PELOriginalNegationSchemePointAction318
public import PELOriginalTripleComplexPoints318
public section
noncomputable section
namespace PELOriginalSchemeAdditionOperations318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalAdditionSchemeMorphism318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- The actual original zero point, as a section of the complex structure map. -/
@[expose] def zeroPoint : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ :=
  candidateComplexPoint τ hτ 0

@[reassoc] lemma zero_over : zeroPoint τ hτ≫π τ hτ=𝟙 _ :=
  PELOriginalProperComplexCandidate318.candidate_point_over τ hτ 0

/-- The independently algebraized projective negation, not a map defined
by transport through complex points. -/
abbrev inverse : candidate τ hτ ⟶ candidate τ hτ :=
  PELOriginalProjectiveNegation318.candidateNegation τ hτ

@[reassoc] lemma inverse_over : inverse τ hτ≫π τ hτ=π τ hτ :=
  PELOriginalNegationComplexBase318.candidate_over_complex τ hτ

lemma inverse_action (q : Base τ) :
    candidateComplexPoint τ hτ q≫inverse τ hτ=candidateComplexPoint τ hτ (-q) := by
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  rw [PELOriginalNegationSchemePointAction318.original_scheme_point_action]
  exact congrArg (candidateComplexPoint τ hτ) (map_neg (QuotientAddGroup.mk' (P τ)) z)

/-- Sum of two genuine candidate-valued morphisms over the same base,
using the actual fiber product and the constructed regular addition. -/
@[expose] def combine {Y : Scheme} (f g : Y ⟶ candidate τ hτ)
    (h : f≫π τ hτ=g≫π τ hτ) : Y ⟶ candidate τ hτ :=
  pullback.lift f g h≫addition τ hτ

@[reassoc] lemma combine_over {Y : Scheme} (f g : Y ⟶ candidate τ hτ)
    (h : f≫π τ hτ=g≫π τ hτ) : combine τ hτ f g h≫π τ hτ=f≫π τ hτ := by
  rw [combine,Category.assoc,over_complex,baseMap,←Category.assoc,pullback.lift_fst]

lemma combine_action {Y : Scheme} (f g : Y ⟶ candidate τ hτ)
    (h : f≫π τ hτ=g≫π τ hτ) (p : Spec (CommRingCat.of ℂ) ⟶ Y)
    (q r : Base τ) (hf : p≫f=candidateComplexPoint τ hτ q)
    (hg : p≫g=candidateComplexPoint τ hτ r) :
    p≫combine τ hτ f g h=candidateComplexPoint τ hτ (q+r) := by
  have he : p≫pullback.lift f g h=pair τ hτ q r := by
    apply pullback.hom_ext
    · rw [Category.assoc,pullback.lift_fst,pair_fst,hf]
    · rw [Category.assoc,pullback.lift_snd,pair_snd,hg]
  rw [combine,←Category.assoc,he,pair_action]

/-- Naturality is a categorical pullback identity for arbitrary test
schemes, including nonreduced schemes. It does not use complex points. -/
theorem combine_naturality {Y Z : Scheme} (k : Z ⟶ Y)
    (f g : Y ⟶ candidate τ hτ) (h : f≫π τ hτ=g≫π τ hτ)
    (h' : (k≫f)≫π τ hτ=(k≫g)≫π τ hτ) :
    k≫combine τ hτ f g h=combine τ hτ (k≫f) (k≫g) h' := by
  have he : k≫pullback.lift f g h=pullback.lift (k≫f) (k≫g) h' := by
    apply pullback.hom_ext <;> simp only [Category.assoc,pullback.lift_fst,pullback.lift_snd]
  rw [combine,combine,←Category.assoc,he]

/-- All original points detect actual candidate-valued scheme maps.
Reducedness and finite type are used, not an unsupported pointwise ext. -/
theorem unary_ext (f g : candidate τ hτ ⟶ candidate τ hτ)
    (hf : f≫π τ hτ=π τ hτ) (hg : g≫π τ hτ=π τ hτ)
    (h : ∀ q : Base τ, candidateComplexPoint τ hτ q≫f=
      candidateComplexPoint τ hτ q≫g) : f=g := by
  apply ReducedComplexPointMorphisms318.ext (π τ hτ) (π τ hτ) f g hf hg
  intro p hp
  obtain ⟨j,z,hz,hze⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ p hp
  rw [hze,PELOriginalChartSchemePointIdentity318.chart_point]
  exact h _
end PELOriginalSchemeAdditionOperations318
