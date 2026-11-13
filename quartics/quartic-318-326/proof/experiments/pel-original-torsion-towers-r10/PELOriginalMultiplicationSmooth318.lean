module
public import PELOriginalFiniteSurjectiveMultiplication318
public import PELOriginalProperSmoothGroup318
public import PELOriginalTranslationAutomorphisms318
public import DominantComplexGenericSmooth318
public import SmoothLocusTargetIso318
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public section
noncomputable section
namespace PELOriginalMultiplicationSmooth318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalIntegerMultiplication318 PELOriginalTranslationAutomorphisms318
open PELOriginalSchemePointGroup318 PELOriginalTorusPointAddEquiv318
open PELOriginalPolarizationTransitions318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) :=
  PELOriginalCandidateIntegral318.integral τ hτ
local instance candidateNoetherian : IsLocallyNoetherian (candidate τ hτ) :=
  LocallyOfFiniteType.isLocallyNoetherian (π τ hτ)

lemma closed_representation (x : candidate τ hτ) (hx : IsClosed ({x} : Set (candidate τ hτ))) :
    ∃ q : Base τ,candidateComplexPoint τ hτ q (IsLocalRing.closedPoint ℂ)=x := by
  let p : Points τ hτ (Spec (CommRingCat.of ℂ)) (𝟙 _) :=
    ⟨pointOfClosedPoint (π τ hτ) x hx,pointOfClosedPoint_comp (π τ hτ) x hx⟩
  obtain ⟨q,hq⟩ := (originalAddEquiv τ hτ).surjective p
  refine ⟨q,?_⟩
  have he := congrArg (fun s : Points τ hτ (Spec (CommRingCat.of ℂ)) (𝟙 _) =>
    s.val (IsLocalRing.closedPoint ℂ)) hq
  exact he.trans (pointOfClosedPoint_apply (π τ hτ) x hx _)

/-- Smoothness of the full nonzero multiplication map. Its actual
characteristic-zero generic field map supplies a nonempty smooth open;
source and target translation isomorphisms spread that open to all closed
points, and the genuine Jacobson property covers every scheme prime. -/
lemma smooth (n : ℤ) (hn : n≠0) : Smooth (multiplication τ hτ n) := by
  let f := multiplication τ hτ n
  letI : IsFinite f := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI : IsDominant f := ⟨(PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn).denseRange⟩
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
  obtain ⟨qx,hqx⟩ := closed_representation τ hτ x hxc
  obtain ⟨qy,hqy⟩ := closed_representation τ hτ y hyc
  let δ : Base τ := qy-qx
  have hxy : translation τ hτ δ x=y := by
    rw [←hqx,←Scheme.Hom.comp_apply,original_action]
    have hq : qx+δ=qy := by dsimp [δ]; abel
    rw [hq,hqy]
  have hinv : translation τ hτ δ ⁻¹ᵁ f.smoothLocus=f.smoothLocus :=
    SmoothLocusTargetIso318.invariant f (translationIso τ hτ δ)
      (translationIso τ hτ (n • δ)) (multiplication_translation τ hτ n δ)
  have hm : x∈translation τ hτ δ ⁻¹ᵁ f.smoothLocus := by
    change translation τ hτ δ x∈f.smoothLocus
    rw [hxy]
    exact hy
  rw [hinv] at hm
  exact hx hm

/-- Actual flatness, not inferred from the cardinality of complex fibers. -/
lemma flat (n : ℤ) (hn : n≠0) : Flat (multiplication τ hτ n) := by
  letI := smooth τ hτ n hn
  infer_instance

/-- Genuine finite, flat, surjective multiplication on the original
candidate. These are full scheme properties; no reduction of the kernel
or comparison with a represented dual is assumed. -/
lemma finite_flat_surjective (n : ℤ) (hn : n≠0) :
    IsFinite (multiplication τ hτ n) ∧ Flat (multiplication τ hτ n) ∧
      Function.Surjective (multiplication τ hτ n) :=
  ⟨PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn,
    flat τ hτ n hn,PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn⟩
end PELOriginalMultiplicationSmooth318
