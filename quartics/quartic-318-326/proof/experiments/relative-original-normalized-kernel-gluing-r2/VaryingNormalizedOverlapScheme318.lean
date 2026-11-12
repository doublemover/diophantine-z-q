module
public import VaryingNormalizedOverlapFrames318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace VaryingNormalizedOverlapScheme318
open AlgebraicGeometry CategoryTheory VaryingNormalizedWordOverlap318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v : ι → List A)
local notation "N" t => VaryingNormalizedWordParameter318.ring R A ι t
local notation "H" s t => VaryingNormalizedWordOverlap318.ring R A ι s t
abbrev chart : Scheme := Spec (CommRingCat.of (N w))
abbrev overlap : Scheme := Spec (CommRingCat.of (H w v))
@[expose] def into : overlap R A ι w v ⟶ chart R A ι w :=
  Spec.map (CommRingCat.ofHom (algebraMap (N w) (H w v)))
instance into_open : IsOpenImmersion (into R A ι w v) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (delta R A ι w v)

/-- The actual transition at the universal overlap point defines a regular
map on the localized coordinate rings. Inverse/cocycle identities for this
ring map require coefficient naturality, separately from the point equivalence. -/
@[expose] def transitionRing : H v w →ₐ[R] H w v :=
  (pointsOnOpen R A ι v (H w v) w).symm
    (VaryingNormalizedOverlapFrames318.transition R A ι w (H w v) v
      (pointsOnOpen R A ι w (H w v) v (AlgHom.id R (H w v))))
@[expose] def transition : overlap R A ι w v ⟶ overlap R A ι v w :=
  Spec.map (CommRingCat.ofHom (transitionRing R A ι w v).toRingHom)

lemma transition_universal :
    pointsOnOpen R A ι v (H w v) w (transitionRing R A ι w v)=
      VaryingNormalizedOverlapFrames318.transition R A ι w (H w v) v
        (pointsOnOpen R A ι w (H w v) v (AlgHom.id R (H w v))) :=
  (pointsOnOpen R A ι v (H w v) w).apply_symm_apply _

@[expose] def projection : overlap R A ι w v ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (H w v)))
@[reassoc] lemma transition_over_base :
    transition R A ι w v ≫ projection R A ι v w=projection R A ι w v := by
  rw [transition,projection,projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact (transitionRing R A ι w v).commutes r
end VaryingNormalizedOverlapScheme318
