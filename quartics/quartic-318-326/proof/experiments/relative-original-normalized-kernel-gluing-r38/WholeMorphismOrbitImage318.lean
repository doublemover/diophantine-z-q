module
public import WholeMorphismOrbitPresheaf318
public section
noncomputable section
namespace WholeMorphismOrbitImage318
open CategoryTheory Opposite
open WholeMorphismOrbitPresheaf318
universe u v w
variable {C : Type u} [Category.{v} C] {Y F : Cᵒᵖ ⥤ Type w} (φ : Y ⟶ F)
/-- Quotienting exact fibers preserves the COMPLETE image sieve on
all test objects, including empty fibers. -/
lemma image_sieve (T : C) (x : F.obj (op T)) :
    Presheaf.imageSieve (inclusion φ) x=Presheaf.imageSieve φ x := by
  ext U f
  change (∃ q : Object φ (op U),(inclusion φ).app (op U) q=F.map f.op x) ↔
    ∃ z : Y.obj (op U),φ.app (op U) z=F.map f.op x
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,rfl⟩ := quotient_surjective φ (op U) q
    exact ⟨z,hq⟩
  · rintro ⟨z,hz⟩
    exact ⟨(quotient φ).app (op U) z,hz⟩
variable (J : GrothendieckTopology C)
instance locallyInjective : Presheaf.IsLocallyInjective J (inclusion φ) :=
  Presheaf.isLocallyInjective_of_injective J (inclusion φ) (inclusion_injective φ)
instance locallySurjective [Presheaf.IsLocallySurjective J φ] :
    Presheaf.IsLocallySurjective J (inclusion φ) where
  imageSieve_mem {T} x := by
    rw [image_sieve]
    exact Presheaf.imageSieve_mem J φ x
end WholeMorphismOrbitImage318
