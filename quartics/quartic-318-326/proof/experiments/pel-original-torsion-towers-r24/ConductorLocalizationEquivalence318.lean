module
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ConductorLocalizationEquivalence318
variable {R A : Type*} [CommRing R] [CommRing A]

/-- An actual conductor gives equality of the WHOLE localized rings.
Only the specified conductor element is inverted. -/
theorem bijective (f : R →+* A) (hf : Function.Injective f) (c : R)
    (hc : ∀ a : A, ∃ b : R, f c * a = f b) :
    Function.Bijective (Localization.awayMap f c) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have h : a = 0 := hf (ha.trans (map_zero f).symm)
    exact ⟨0,by simp [h]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro a
    obtain ⟨b,hb⟩ := hc a
    exact ⟨b,1,by simpa only [pow_one] using hb.symm⟩

/-- The equivalence is induced by the original inclusion, not an
unrelated abstract isomorphism of the two localized rings. -/
@[expose] def equivalence (f : R →+* A) (hf : Function.Injective f) (c : R)
    (hc : ∀ a : A, ∃ b : R, f c * a = f b) :
    Localization.Away c ≃+* Localization.Away (f c) :=
  RingEquiv.ofBijective (Localization.awayMap f c) (bijective f hf c hc)

@[simp] theorem equivalence_algebraMap (f : R →+* A) (hf : Function.Injective f)
    (c : R) (hc : ∀ a : A, ∃ b : R, f c * a = f b) (r : R) :
    equivalence f hf c hc (algebraMap R (Localization.Away c) r) =
      algebraMap A (Localization.Away (f c)) (f r) := by
  change Localization.awayMap f c (algebraMap R (Localization.Away c) r) = _
  simp only [Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq]

/-- With an actual scalar-preserving inclusion, the same localization
map preserves the original scalar action on both entire rings. -/
@[expose] def algEquivalence {B : Type*} [CommRing B] [Algebra B R] [Algebra B A]
    (f : R →ₐ[B] A) (hf : Function.Injective f) (c : R)
    (hc : ∀ a : A, ∃ b : R, f c * a = f b) :
    Localization.Away c ≃ₐ[B] Localization.Away (f c) :=
  { equivalence f.toRingHom hf c hc with
    commutes' b := by
      change Localization.awayMap f.toRingHom c
        (algebraMap B (Localization.Away c) b) = _
      rw [IsScalarTower.algebraMap_apply B R (Localization.Away c),
        IsScalarTower.algebraMap_apply B A (Localization.Away (f c))]
      simp only [Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq,
        AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes] }
end ConductorLocalizationEquivalence318
