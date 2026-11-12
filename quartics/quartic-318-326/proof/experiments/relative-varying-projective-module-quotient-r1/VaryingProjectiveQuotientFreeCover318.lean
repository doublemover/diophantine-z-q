module
public import VaryingProjectiveQuotientLocalBasis318
public import VaryingLocalFreeIdealCover318
public section
noncomputable section
namespace VaryingProjectiveQuotientFreeCover318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : Ideal (S ⊗[R] A))
  [Module.Finite S ((S ⊗[R] A) ⧸ I)] [Module.Projective S ((S ⊗[R] A) ⧸ I)]
  (h : ∀ x : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R] A) ⧸ I) x=Fintype.card ι)
@[expose] def denominator (x : PrimeSpectrum S) : S :=
  (VaryingProjectiveQuotientLocalBasis318.exists_extended_basis R A ι S I h x).choose
lemma denominator_notMem (x : PrimeSpectrum S) : denominator R A ι S I h x∉x.asIdeal :=
  (VaryingProjectiveQuotientLocalBasis318.exists_extended_basis R A ι S I h x).choose_spec.1
/-- A whole affine coefficient cover from the module-theoretic input
alone. Every prime is covered by its actual principal neighborhood. -/
@[expose] def coefficients : AffineCoefficientCover318.Data R S where
  Index := PrimeSpectrum S
  ring x := CommRingCat.of (Localization.Away (denominator R A ι S I h x))
  algebra := fun x => inferInstance
  coefficient x := IsScalarTower.toAlgHom R S _
  open_map x := Scheme.isOpenImmersion_SpecMap_localizationAway (denominator R A ι S I h x)
  covers x := by
    refine ⟨x,?_⟩
    change x ∈ Set.range (PrimeSpectrum.comap (algebraMap S
      (Localization.Away (denominator R A ι S I h x))))
    rw [PrimeSpectrum.localization_away_comap_range]
    exact denominator_notMem R A ι S I h x
/-- Independent geometric local-freeness is a CONSEQUENCE of actual
finite projectivity and stalk rank, not an extra input assumption. -/
@[expose] def data : VaryingLocalFreeIdealCover318.Data R A ι S I where
  coefficients := coefficients R A ι S I h
  free x := (VaryingProjectiveQuotientLocalBasis318.exists_extended_basis R A ι S I h x).choose_spec.2
end VaryingProjectiveQuotientFreeCover318
