module
public import VaryingWordTripleCocycle318
public import AffineAwayPullback318
public section
noncomputable section
namespace VaryingWordTriplePullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingWordTripleMaps318 VaryingWordTripleCocycle318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "N" x => VaryingNormalizedWordParameter318.ring R A ι x
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "f" => CommRingCat.ofHom (algebraMap (N w) (H w v))
local notation "x" => VaryingNormalizedWordOverlap318.delta R A ι w u
abbrev scheme : Scheme := Spec (CommRingCat.of (K w v u))
@[expose] def first : scheme R A ι w v u ⟶ VaryingNormalizedOverlapScheme318.overlap R A ι w v :=
  Spec.map (CommRingCat.ofHom (firstMap R A ι w v u).toRingHom)
@[expose] def second : scheme R A ι w v u ⟶ VaryingNormalizedOverlapScheme318.overlap R A ι w u :=
  Spec.map (CommRingCat.ofHom (secondMap R A ι w v u).toRingHom)

lemma second_ring : CommRingCat.ofHom (secondMap R A ι w v u).toRingHom=
    AffineAwayPullback318.arrow f x := by
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  apply RingHom.ext
  intro z
  exact (second_base R A ι w v u z).trans (AffineAwayPullback318.arrow_base f x z).symm

/-- The actual iterated determinant localization is the required scheme
pullback, with the exact represented first and second overlap projections. -/
lemma cartesian : IsPullback (first R A ι w v u) (second R A ι w v u)
    (VaryingNormalizedOverlapScheme318.into R A ι w v)
    (VaryingNormalizedOverlapScheme318.into R A ι w u) := by
  rw [second,second_ring]
  exact AffineAwayPullback318.pullback f x
@[expose] def comparison : scheme R A ι w v u ≅
    pullback (VaryingNormalizedOverlapScheme318.into R A ι w v)
      (VaryingNormalizedOverlapScheme318.into R A ι w u) :=
  (cartesian R A ι w v u).isoPullback
@[reassoc] lemma comparison_fst : (comparison R A ι w v u).hom ≫ pullback.fst _ _=first R A ι w v u :=
  (cartesian R A ι w v u).isoPullback_hom_fst
@[reassoc] lemma comparison_snd : (comparison R A ι w v u).hom ≫ pullback.snd _ _=second R A ι w v u :=
  (cartesian R A ι w v u).isoPullback_hom_snd

@[expose] def rotation : scheme R A ι w v u ⟶ scheme R A ι v u w :=
  Spec.map (CommRingCat.ofHom (rotateMap R A ι w v u).toRingHom)
@[reassoc] lemma rotation_leg : rotation R A ι w v u ≫ second R A ι v u w=
    first R A ι w v u ≫ VaryingNormalizedOverlapScheme318.transition R A ι w v := by
  rw [rotation,second,first,VaryingNormalizedOverlapScheme318.transition,← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (VaryingWordTripleCocycle318.leg R A ι w v u)
lemma rotation_cycle : rotation R A ι w v u ≫ rotation R A ι v u w ≫ rotation R A ι u w v=𝟙 _ := by
  unfold rotation
  rw [← Spec.map_comp,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((rotateMap R A ι w v u).comp (rotateMap R A ι v u w)).comp
      (rotateMap R A ι u w v)).toRingHom)=_
  rw [VaryingWordTripleCocycle318.cycle]
  exact Spec.map_id _
end VaryingWordTriplePullback318
