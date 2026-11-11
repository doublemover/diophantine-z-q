module
public import PELOriginalMultiplicationSmooth318
public import DominantComplexGenericUnramified318
public import UnramifiedLocusTargetIso318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public section
noncomputable section
namespace PELOriginalMultiplicationEtale318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalIntegerMultiplication318 PELOriginalTranslationAutomorphisms318
open PELOriginalSchemePointGroup318 PELOriginalTorusPointAddEquiv318
open PELOriginalPolarizationTransitions318 PELOriginalMultiplicationSmooth318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) :=
  PELOriginalCandidateIntegral318.integral τ hτ
local instance candidateNoetherian : IsLocallyNoetherian (candidate τ hτ) :=
  LocallyOfFiniteType.isLocallyNoetherian (π τ hτ)

/-- Formal unramifiedness of the full nonzero multiplication map. Its actual
characteristic-zero generic field map supplies a nonempty unramified open;
source and target translation isomorphisms spread that open to all closed
points, and the genuine Jacobson property covers every scheme prime. -/
lemma unramified (n : ℤ) (hn : n≠0) : FormallyUnramified (multiplication τ hτ n) := by
  let f := multiplication τ hτ n
  letI : IsFinite f := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI : IsDominant f := ⟨(PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn).denseRange⟩
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
  obtain ⟨qx,hqx⟩ := closed_representation τ hτ x hxc
  obtain ⟨qy,hqy⟩ := closed_representation τ hτ y hyc
  let δ : Base τ := qy-qx
  have hxy : translation τ hτ δ x=y := by
    rw [←hqx,←Scheme.Hom.comp_apply,original_action]
    have hq : qx+δ=qy := by dsimp [δ]; abel
    rw [hq,hqy]
  have hinv : translation τ hτ δ ⁻¹ᵁ (SchemeUnramifiedLocus318.locus f)=(SchemeUnramifiedLocus318.locus f) :=
    UnramifiedLocusTargetIso318.invariant f (translationIso τ hτ δ)
      (translationIso τ hτ (n • δ)) (multiplication_translation τ hτ n δ)
  have hm : x∈translation τ hτ δ ⁻¹ᵁ (SchemeUnramifiedLocus318.locus f) := by
    change translation τ hτ δ x∈(SchemeUnramifiedLocus318.locus f)
    rw [hxy]
    exact hy
  rw [hinv] at hm
  exact hx hm

/-- Genuine étaleness of the WHOLE original multiplication map,
combining its independently produced flatness with its native unramified locus. -/
lemma etale (n : ℤ) (hn : n≠0) : Etale (multiplication τ hτ n) := by
  letI := PELOriginalMultiplicationSmooth318.smooth τ hτ n hn
  letI := unramified τ hτ n hn
  exact Etale.of_formallyUnramified_of_flat _

lemma finite_etale_surjective (n : ℤ) (hn : n≠0) :
    IsFinite (multiplication τ hτ n) ∧ Etale (multiplication τ hτ n) ∧
      Function.Surjective (multiplication τ hτ n) :=
  ⟨PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn,
    etale τ hτ n hn,PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn⟩
end PELOriginalMultiplicationEtale318
