module
public import PELOriginalFiniteOrderIsogeny318
public import PELOriginalMultiplicationEtale318
public import PELOriginalOrderKernelScheme318
public section
noncomputable section
namespace PELOriginalEtaleOrderIsogeny318
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
/-- Formal unramifiedness of the actual original nonzero reduced-norm order map. Its actual
characteristic-zero generic field map supplies a nonempty unramified open;
source and target translation isomorphisms spread that open to all closed
points, and the genuine Jacobson property covers every scheme prime. -/
lemma unramified (a : order) (ha : norm a≠0) : FormallyUnramified (morphism τ hτ a) := by
  let f := morphism τ hτ a
  letI : IsFinite f := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI : IsDominant f := ⟨(PELOriginalOrderNormComposites318.surjective τ hτ a ha).denseRange⟩
  have := LocallyOfFiniteType.jacobsonSpace (π τ hτ)
  have hg : genericPoint (candidate τ hτ)∈(SchemeUnramifiedLocus318.locus f) :=
    DominantComplexGenericUnramified318.generic_mem (π τ hτ) f
  rw [←SchemeUnramifiedLocus318.locus_eq_top_iff,←TopologicalSpace.Opens.coe_eq_univ,
    ←not_ne_iff,←Set.nonempty_compl]
  intro H
  obtain ⟨x,hx,hxc⟩ := nonempty_inter_closedPoints H (SchemeUnramifiedLocus318.locus f).2.isClosed_compl.isLocallyClosed
  obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints
    (show ((SchemeUnramifiedLocus318.locus f) : Set (candidate τ hτ)).Nonempty from ⟨_,hg⟩)
    (SchemeUnramifiedLocus318.locus f).2.isLocallyClosed
  obtain ⟨qx,hqx⟩ := PELOriginalMultiplicationSmooth318.closed_representation τ hτ x hxc
  obtain ⟨qy,hqy⟩ := PELOriginalMultiplicationSmooth318.closed_representation τ hτ y hyc
  let δ : Base τ := qy-qx
  have hxy : translation τ hτ δ x=y := by
    rw [←hqx,←Scheme.Hom.comp_apply,original_action]
    have hq : qx+δ=qy := by dsimp [δ]; abel
    rw [hq,hqy]
  have hinv : translation τ hτ δ ⁻¹ᵁ (SchemeUnramifiedLocus318.locus f)=(SchemeUnramifiedLocus318.locus f) :=
    UnramifiedLocusTargetIso318.invariant f (translationIso τ hτ δ)
      (translationIso τ hτ (orderEnd representation order τ a δ))
      (PELOriginalOrderAutomorphisms318.translation_square τ hτ a δ)
  have hm : x∈translation τ hτ δ ⁻¹ᵁ (SchemeUnramifiedLocus318.locus f) := by
    change translation τ hτ δ x∈(SchemeUnramifiedLocus318.locus f)
    rw [hxy]
    exact hy
  rw [hinv] at hm
  exact hx hm

/-- Every original order element with NONZERO reduced norm gives a
finite étale surjective map, retaining the original scheme endomorphism. -/
lemma etale (a : order) (ha : norm a≠0) : Etale (morphism τ hτ a) := by
  letI := PELOriginalSmoothOrderIsogeny318.smooth τ hτ a ha
  letI := unramified τ hτ a ha
  exact Etale.of_formallyUnramified_of_flat _
lemma finite_etale_surjective (a : order) (ha : norm a≠0) :
    IsFinite (morphism τ hτ a) ∧ Etale (morphism τ hτ a) ∧
      Function.Surjective (morphism τ hτ a) :=
  ⟨PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha,etale τ hτ a ha,
    PELOriginalOrderNormComposites318.surjective τ hτ a ha⟩

lemma kernel_finite_etale (a : order) (ha : norm a≠0) :
    IsFinite (PELOriginalOrderKernelScheme318.structureMap τ hτ a) ∧
    Etale (PELOriginalOrderKernelScheme318.structureMap τ hτ a) := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI := etale τ hτ a ha
  exact ⟨inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd
      (morphism τ hτ a) (PELOriginalSchemeGroupUnitInverse318.zeroPoint τ hτ))),
    inferInstanceAs (Etale (CategoryTheory.Limits.pullback.snd
      (morphism τ hτ a) (PELOriginalSchemeGroupUnitInverse318.zeroPoint τ hτ)))⟩
end PELOriginalEtaleOrderIsogeny318
