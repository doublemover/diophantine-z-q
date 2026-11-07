module

public import EtaleInvariantQuotient318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open InvariantBaseChange318 EtaleInvariantQuotient318

namespace OrbitQuotientScheme318

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {G X : Type u} [Group G] [MulAction G X]

/-- The actual affine quotient scheme, the spectrum of the fixed coordinate algebra. -/
def quotientScheme (ρ : G → B ≃ₐ[R] B) : Scheme :=
  Spec (CommRingCat.of (invariants ρ))

/-- Its actual structure morphism to the base scheme. -/
def structureMap (ρ : G → B ≃ₐ[R] B) : quotientScheme ρ ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (invariants ρ)))

/-- The actual map from the original affine cover to the quotient. -/
def quotientMap (ρ : G → B ≃ₐ[R] B) : Spec (CommRingCat.of B) ⟶ quotientScheme ρ :=
  Spec.map (CommRingCat.ofHom (algebraMap (invariants ρ) B))

/-- The quotient structure map is finite étale from the actual equivariant splitting. -/
theorem structure_finite_etale (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Finite G] [Finite X]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x)) :
    IsFinite (structureMap ρ) ∧ Etale (structureMap ρ) := by
  obtain ⟨hf, he'⟩ := finite_etale_of_faithfullyFlat_split S ρ e he
  letI := hf
  letI := he'
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr hf
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact (RingHom.etale_algebraMap).mpr he'

/-- The original affine cover is finite étale over the constructed quotient scheme. -/
theorem quotient_finite_etale (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Finite G] [Finite X]
    (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
    (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
      e (baseAction S ρ g b) x = e b (g • x)) :
    IsFinite (quotientMap ρ) ∧ Etale (quotientMap ρ) := by
  obtain ⟨hf, he'⟩ := quotient_map_finite_etale S ρ e he
  letI := hf
  letI := he'
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr hf
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact (RingHom.etale_algebraMap).mpr he'

/-- Every supplied automorphism acts trivially after passage to the quotient. -/
theorem quotientMap_invariant (ρ : G → B ≃ₐ[R] B) (g : G) :
    Spec.map (CommRingCat.ofHom (ρ g).toRingHom) ≫ quotientMap ρ = quotientMap ρ := by
  unfold quotientMap quotientScheme
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact b.property g

end OrbitQuotientScheme318
