module

public import OrbitQuotientScheme318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open InvariantBaseChange318 EtaleInvariantQuotient318 OrbitQuotientScheme318

namespace EtaleQuotientCover318

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {G X : Type u} [Group G] [MulAction G X]
variable (S : Type u) [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] [Finite G] [Finite X]
variable (ρ : G → B ≃ₐ[R] B) (e : S ⊗[R] B ≃ₐ[S] (X → S))
variable (he : ∀ (g : G) (b : S ⊗[R] B) (x : X),
    e (baseAction S ρ g b) x = e b (g • x))

include S e he
/-- The actual quotient inclusion is faithfully flat, not merely etale. -/
theorem quotient_faithfullyFlat : Module.FaithfullyFlat (invariants ρ) B := by
  obtain ⟨hf, he'⟩ := quotient_map_finite_etale S ρ e he
  letI := hf
  letI := he'
  letI : FaithfulSMul (invariants ρ) B :=
    (faithfulSMul_iff_algebraMap_injective (invariants ρ) B).mpr Subtype.val_injective
  exact Module.FaithfullyFlat.of_comap_surjective
    (Algebra.IsIntegral.comap_surjective (invariants ρ) B)

/-- The constructed actual scheme quotient is surjective. -/
theorem quotient_surjective : Surjective (quotientMap ρ) := by
  have h := quotient_faithfullyFlat S ρ e he
  exact (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (invariants ρ) B))).mpr
      ((RingHom.faithfullyFlat_algebraMap_iff).mpr h) |>.2

/-- The actual quotient morphism is a surjective finite-etale cover. -/
theorem quotient_cover : IsFinite (quotientMap ρ) ∧
    Etale (quotientMap ρ) ∧ Surjective (quotientMap ρ) :=
  ⟨(quotient_finite_etale S ρ e he).1,
    (quotient_finite_etale S ρ e he).2, quotient_surjective S ρ e he⟩

/-- On underlying spaces the actual quotient map is a quotient map. -/
theorem quotient_topological : Topology.IsQuotientMap (quotientMap ρ) := by
  obtain ⟨hf, he', hs⟩ := quotient_cover S ρ e he
  letI := hf
  letI := he'
  letI := hs
  exact AlgebraicGeometry.Flat.isQuotientMap_of_surjective (quotientMap ρ)

end EtaleQuotientCover318
