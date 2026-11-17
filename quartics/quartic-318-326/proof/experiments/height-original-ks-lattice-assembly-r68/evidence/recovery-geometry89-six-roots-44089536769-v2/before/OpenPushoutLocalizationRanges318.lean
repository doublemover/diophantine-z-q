module
public import GenericOpenPushout318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace OpenPushoutLocalizationRanges318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]

theorem left_cross :
    (pushout.inl f g) ⁻¹ᵁ (pushout.inr f g).opensRange = f.opensRange := by
  ext x
  change (pushout.inl f g x ∈ Set.range (pushout.inr f g)) ↔ x ∈ Set.range f
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := GenericOpenPushout318.exists_overlap f g x y hy.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨g z, congrArg (fun k => k z) (pushout.condition (f := f) (g := g)).symm⟩

theorem right_cross :
    (pushout.inr f g) ⁻¹ᵁ (pushout.inl f g).opensRange = g.opensRange := by
  ext y
  change (pushout.inr f g y ∈ Set.range (pushout.inl f g)) ↔ y ∈ Set.range g
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, _, hz⟩ := GenericOpenPushout318.exists_overlap f g x y hx
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f z, congrArg (fun k => k z) (pushout.condition (f := f) (g := g))⟩

/-- An exact principal localization square on underlying spectra. The
source localization must invert the IMAGE of the target parameter; no
arbitrary localization or finiteness assumption substitutes for this. -/
theorem away_preimage {A B A' B' : Type*} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
    (h : A →+* B) (x : A) [IsLocalization.Away x A']
    [IsLocalization.Away (h x) B'] :
    PrimeSpectrum.comap h ⁻¹' Set.range (PrimeSpectrum.comap (algebraMap A A')) =
      Set.range (PrimeSpectrum.comap (algebraMap B B')) := by
  rw [PrimeSpectrum.localization_away_comap_range A' x,
    PrimeSpectrum.localization_away_comap_range B' (h x)]
  exact congrArg (fun V : (PrimeSpectrum B).Opens => (V : Set (PrimeSpectrum B)))
    (PrimeSpectrum.comap_basicOpen h x)

end OpenPushoutLocalizationRanges318
