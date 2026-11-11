module
public import VaryingWordTransitionNaturality318
public section
noncomputable section
namespace VaryingWordOverlapIso318
open VaryingNormalizedWordOverlap318 VaryingNormalizedOverlapFrames318
open VaryingWordTransitionNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v : ι → List A)
local notation "H" s t => VaryingNormalizedWordOverlap318.ring R A ι s t

lemma transition_inverse (S : Type u) [CommRing S] [Algebra R S]
    (d : Point R A ι w S v) :
    transition R A ι v S w (transition R A ι w S v d)=d :=
  (transition R A ι w S v).symm_apply_apply d

/-- Evaluation of the regular universal ring map agrees with the actual
normalization on every coefficient test, not just at the universal point. -/
lemma transitionRing_evaluate (S : Type u) [CommRing S] [Algebra R S]
    (a : H w v →ₐ[R] S) :
    pointsOnOpen R A ι v S w
      (a.comp (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v))=
      transition R A ι w S v (pointsOnOpen R A ι w S v a) := by
  rw [show pointsOnOpen R A ι v S w
      (a.comp (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v))=
        mapPoint R A ι v (H w v) w S a
          (pointsOnOpen R A ι v (H w v) w
            (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v)) from
    toPoint_natural R A ι v (H w v) w S a _]
  rw [VaryingNormalizedOverlapScheme318.transition_universal,transition_natural]
  have h := toPoint_natural R A ι w (H w v) v S a (AlgHom.id R (H w v))
  simp only [AlgHom.comp_id] at h
  exact congrArg (transition R A ι w S v) h.symm

lemma transitionRing_inverse :
    (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v).comp
      (VaryingNormalizedOverlapScheme318.transitionRing R A ι v w)=AlgHom.id R (H w v) := by
  apply (pointsOnOpen R A ι w (H w v) v).injective
  rw [transitionRing_evaluate,VaryingNormalizedOverlapScheme318.transition_universal]
  exact transition_inverse R A ι w v (H w v) _

@[expose] def ringEquiv : H v w ≃ₐ[R] H w v :=
  AlgEquiv.ofAlgHom
    (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v)
    (VaryingNormalizedOverlapScheme318.transitionRing R A ι v w)
    (transitionRing_inverse R A ι w v) (transitionRing_inverse R A ι v w)

/-- Genuine regular overlap isomorphism, with inverse checked as an
identity of the actual localized coordinate-ring homomorphisms. -/
@[expose] def overlapIso :
    VaryingNormalizedOverlapScheme318.overlap R A ι w v ≅
      VaryingNormalizedOverlapScheme318.overlap R A ι v w where
  hom := VaryingNormalizedOverlapScheme318.transition R A ι w v
  inv := VaryingNormalizedOverlapScheme318.transition R A ι v w
  hom_inv_id := by
    change Spec.map _ ≫ Spec.map _=𝟙 _
    rw [← Spec.map_comp,← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (transitionRing_inverse R A ι w v)
  inv_hom_id := by
    change Spec.map _ ≫ Spec.map _=𝟙 _
    rw [← Spec.map_comp,← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (transitionRing_inverse R A ι v w)
end VaryingWordOverlapIso318
