module
public import ActualLocalizationCartesian318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ActualPrincipalOpenRestriction318
open AlgebraicGeometry CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S]

/-- Literal restriction between original principal localizations.
The target ring is exactly Away(s), not an isomorphic renamed ring. -/
@[expose] def restriction (r s : R) (h : r ∣ s) :
    Localization.Away r →+* Localization.Away s :=
  IsLocalization.Away.lift r (g := algebraMap R (Localization.Away s))
    (IsLocalization.Away.isUnit_of_dvd s h)

@[simp] theorem restriction_source (r s : R) (h : r ∣ s) (a : R) :
    restriction r s h (algebraMap R (Localization.Away r) a) =
      algebraMap R (Localization.Away s) a :=
  IsLocalization.Away.lift_eq r (IsLocalization.Away.isUnit_of_dvd s h) a

theorem restriction_comp_source (r s : R) (h : r ∣ s) :
    (restriction r s h).comp (algebraMap R (Localization.Away r)) =
      algebraMap R (Localization.Away s) := by ext a; exact restriction_source r s h a

/-- The source restriction and base restriction commute for the exact
original ring map. In particular this covers s = r*d without replacing
f(r*d) by a new scalar action on an iterated localization. -/
theorem square (f : R →+* S) (r s : R) (h : r ∣ s) :
    (restriction (f r) (f s) (map_dvd f h)).comp (Localization.awayMap f r) =
      (Localization.awayMap f s).comp (restriction r s h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext a
  simp only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,restriction_source]

@[reassoc] theorem source_composition (r s : R) (h : r ∣ s) :
    Spec.map (CommRingCat.ofHom (restriction r s h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
  rw [←Spec.map_comp]
  congr 1
  ext a
  exact restriction_source r s h a

/-- Restricting in two steps is the same actual original restriction. -/
theorem restriction_trans (r s t : R) (hrs : r ∣ s) (hst : s ∣ t) :
    (restriction s t hst).comp (restriction r s hrs) =
      restriction r t (dvd_trans hrs hst) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext a
  simp only [RingHom.comp_apply,restriction_source]
end ActualPrincipalOpenRestriction318
