module
public import PELOriginalFiniteOrderIsogeny318
public import PELOriginalMultiplicationSmooth318
public section
noncomputable section
namespace PELOriginalSmoothOrderIsogeny318
open AlgebraicGeometry CategoryTheory TopologicalSpace PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalOrderSchemeMorphism318 PELOriginalOrderIntegralNorm318
open PELOriginalTranslationAutomorphisms318 PELOriginalSchemePointGroup318
open PELOriginalPolarizationTransitions318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) :=
  PELOriginalCandidateIntegral318.integral τ hτ
local instance candidateNoetherian : IsLocallyNoetherian (candidate τ hτ) :=
  LocallyOfFiniteType.isLocallyNoetherian (π τ hτ)
/-- Smoothness of the actual original nonzero reduced-norm order map. Its actual
characteristic-zero generic field map supplies a nonempty smooth open;
source and target translation isomorphisms spread that open to all closed
points, and the genuine Jacobson property covers every scheme prime. -/
lemma smooth (a : order) (ha : norm a≠0) : Smooth (morphism τ hτ a) := by
  let f := morphism τ hτ a
  letI : IsFinite f := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI : IsDominant f := ⟨(PELOriginalOrderNormComposites318.surjective τ hτ a ha).denseRange⟩
  have := LocallyOfFiniteType.jacobsonSpace (π τ hτ)
  have hg : genericPoint (candidate τ hτ)∈f.smoothLocus :=
    DominantComplexGenericSmooth318.generic_mem (π τ hτ) f
  rw [←Scheme.Hom.smoothLocus_eq_top_iff,←TopologicalSpace.Opens.coe_eq_univ,
    ←not_ne_iff,←Set.nonempty_compl]
  intro H
  obtain ⟨x,hx,hxc⟩ := nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints
    (show (f.smoothLocus : Set (candidate τ hτ)).Nonempty from ⟨_,hg⟩)
    f.smoothLocus.2.isLocallyClosed
  obtain ⟨qx,hqx⟩ := PELOriginalMultiplicationSmooth318.closed_representation τ hτ x hxc
  obtain ⟨qy,hqy⟩ := PELOriginalMultiplicationSmooth318.closed_representation τ hτ y hyc
  let δ : Base τ := qy-qx
  have hxy : translation τ hτ δ x=y := by
    rw [←hqx,←Scheme.Hom.comp_apply,original_action]
    have hq : qx+δ=qy := by dsimp [δ]; abel
    rw [hq,hqy]
  have hinv : translation τ hτ δ ⁻¹ᵁ f.smoothLocus=f.smoothLocus :=
    SmoothLocusTargetIso318.invariant f (translationIso τ hτ δ)
      (translationIso τ hτ (orderEnd representation order τ a δ))
      (PELOriginalOrderAutomorphisms318.translation_square τ hτ a δ)
  have hm : x∈translation τ hτ δ ⁻¹ᵁ f.smoothLocus := by
    change translation τ hτ δ x∈f.smoothLocus
    rw [hxy]
    exact hy
  rw [hinv] at hm
  exact hx hm

/-- Full finite, flat, surjective order isogeny on the original scheme.
No degree formula or assertion that every nonzero order element has
nonzero reduced norm is hidden in this statement. -/
lemma finite_flat_surjective (a : order) (ha : norm a≠0) :
    IsFinite (morphism τ hτ a) ∧ Flat (morphism τ hτ a) ∧
      Function.Surjective (morphism τ hτ a) := by
  letI := smooth τ hτ a ha
  exact ⟨PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha,inferInstance,
    PELOriginalOrderNormComposites318.surjective τ hτ a ha⟩
end PELOriginalSmoothOrderIsogeny318
