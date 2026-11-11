module
public import ActualPrincipalOpenRestriction318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace ActualFinitePrincipalRestriction318
open AlgebraicGeometry CategoryTheory ActualPrincipalOpenRestriction318
variable {R S : Type} [CommRing R] [CommRing S]

/-- The full original principal-preimage restriction is Cartesian.
This follows from two genuine localization pushouts, not from equality
on complex points or a purported fiberwise bijection. -/
theorem cartesian (f : R →+* S) (r s : R) (h : r ∣ s) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (restriction (f r) (f s) (map_dvd f h))))
      (Spec.map (CommRingCat.ofHom (Localization.awayMap f s)))
      (Spec.map (CommRingCat.ofHom (Localization.awayMap f r)))
      (Spec.map (CommRingCat.ofHom (restriction r s h))) := by
  apply IsPullback.of_right
    (h₁₂ := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f r)))))
    (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
    (v₁₃ := Spec.map (CommRingCat.ofHom f))
    _ _ (ActualLocalizationCartesian318.square f r)
  · simpa only [source_composition] using ActualLocalizationCartesian318.square f s
  · rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    exact square f r s h

/-- A finite original base-open map stays finite on the exact smaller
base open. The source remains the WHOLE original inverse image. -/
theorem finite (f : R →+* S) (r s : R) (h : r ∣ s)
    (hf : (Localization.awayMap f r).Finite) :
    (Localization.awayMap f s).Finite := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (Localization.awayMap f r))) :=
    (IsFinite.SpecMap_iff _).mpr hf
  have hs : IsFinite (Spec.map (CommRingCat.ofHom (Localization.awayMap f s))) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (cartesian f r s h) inferInstance
  exact (IsFinite.SpecMap_iff _).mp hs

/-- Product localization is the actual common open for the finite-map
and separable-polynomial denominators. -/
theorem finite_product (f : R →+* S) (p d : R)
    (hf : (Localization.awayMap f p).Finite) :
    (Localization.awayMap f (p*d)).Finite :=
  finite f p (p*d) (dvd_mul_right p d) hf
end ActualFinitePrincipalRestriction318
