module
public import PELOriginalRepresentedGroupFunctor318
public section
noncomputable section
namespace PELOriginalTorusPointAddEquiv318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalCandidateComplexPoints318 PELOriginalProductChartCover318
open PELOriginalProductComplexPoints318 PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The original theta point map, now a homomorphism to the genuine
algebraic group's full complex-valued point group. -/
@[expose] def originalPoints : Base τ →+
    Points τ hτ (Spec (CommRingCat.of ℂ)) (𝟙 _) where
  toFun q := ⟨candidateComplexPoint τ hτ q,
    PELOriginalProperComplexCandidate318.candidate_point_over τ hτ q⟩
  map_zero' := by
    apply Subtype.ext
    exact (Category.id_comp _).symm
  map_add' q r := by
    apply Subtype.ext
    exact (PELOriginalAdditionSchemeMorphism318.pair_action τ hτ q r).symm

lemma originalPoints_bijective : Function.Bijective (originalPoints τ hτ) := by
  constructor
  · intro q r h
    apply PELOriginalChartSchemePointIdentity318.candidate_point_injective τ hτ
    exact congrArg Subtype.val h
  · intro p
    obtain ⟨j,z,hz,hze⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point
      τ hτ p.val p.property
    refine ⟨projection (P τ) z,?_⟩
    apply Subtype.ext
    change candidateComplexPoint τ hτ (projection (P τ) z)=p.val
    rw [hze,PELOriginalChartSchemePointIdentity318.chart_point]

/-- Exact additive identification with the ORIGINAL analytic torus.
All algebraic group operations were constructed and proved on schemes
before this equivalence; it is not used to transport regularity. -/
@[expose] def originalAddEquiv : Base τ ≃+
    Points τ hτ (Spec (CommRingCat.of ℂ)) (𝟙 _) :=
  AddEquiv.ofBijective (originalPoints τ hτ) (originalPoints_bijective τ hτ)

lemma originalAddEquiv_point (q : Base τ) :
    (originalAddEquiv τ hτ q).val=candidateComplexPoint τ hτ q := rfl
end PELOriginalTorusPointAddEquiv318
