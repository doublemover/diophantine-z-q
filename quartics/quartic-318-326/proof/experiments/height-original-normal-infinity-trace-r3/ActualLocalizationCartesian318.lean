module
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace ActualLocalizationCartesian318
open AlgebraicGeometry CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S]

/-- The literal source localization is the full Scheme-theoretic
inverse image of the base localization. This is an actual pushout of
rings mapped by Spec, not a complex-point calculation. -/
theorem square (f : R →+* S) (r : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f r)))))
      (Spec.map (CommRingCat.ofHom (Localization.awayMap f r)))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
  haveI : IsLocalization ((Submonoid.powers r).map f) (Localization.Away (f r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  have h : (Localization.awayMap f r).comp (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away (f r))).comp f := by
    ext a
    simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
      IsLocalization.map_eq]
  exact (CommRingCat.isPushout_of_isLocalization f
    (Localization.awayMap f r) h (Submonoid.powers r)).op.map Scheme.Spec
end ActualLocalizationCartesian318
