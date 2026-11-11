module
public import CanonicalStalkModule318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace LocalIdealLengthTransport318
open AlgebraicGeometry CategoryTheory
universe u
/-- The quotient equivalence is semilinear over the SAME ring equivalence;
the quotient module actions are the natural ones. -/
def quotientEquiv {R S : Type*} [CommRing R] [CommRing S]
    (σ : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : J = I.map σ.toRingHom) :
    (R ⧸ I) ≃ₛₗ[σ.toRingHom] (S ⧸ J) where
  __ := (Ideal.quotientEquiv I J σ h).toAddEquiv
  map_smul' r x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J (σ (r*x)) = Ideal.Quotient.mk J (σ r * σ x)
    rw [map_mul]
lemma quotient_length {R S : Type*} [CommRing R] [CommRing S]
    (σ : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : J = I.map σ.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) :=
  CanonicalStalkModule318.length_semilinear σ (quotientEquiv σ I J h)
variable {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (q : PrimeSpectrum S)
/-- Actual local-ring equivalence induced by the original affine open
immersion, pinned between the two canonical prime localizations. -/
@[expose] def localizationEquiv :
    Localization.AtPrime (q.comap f).asIdeal ≃+* Localization.AtPrime q.asIdeal :=
  ((Spec.stalkIso (CommRingCat.of R) (q.comap f)).symm ≪≫
    asIso ((Spec.map (CommRingCat.ofHom f)).stalkMap q) ≪≫
    Spec.stalkIso (CommRingCat.of S) q).commRingCatIsoToRingEquiv
lemma localizationEquiv_source (r : R) :
    localizationEquiv f q (algebraMap R _ r) = algebraMap S _ (f r) := by
  have h : (Spec.stalkIso (CommRingCat.of R) (q.comap f)).inv ≫
      (Spec.map (CommRingCat.ofHom f)).stalkMap q ≫
      (Spec.stalkIso (CommRingCat.of S) q).hom =
        CommRingCat.ofHom (Localization.localRingHom (q.comap f).asIdeal q.asIdeal f rfl) := by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp only [Iso.inv_hom_id_assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change ((Spec.stalkIso (CommRingCat.of R) (q.comap f)).inv ≫
      (Spec.map (CommRingCat.ofHom f)).stalkMap q ≫
      (Spec.stalkIso (CommRingCat.of S) q).hom) (algebraMap R _ r) = _
  rw [h]
  exact Localization.localRingHom_to_map _ _ f rfl r
lemma full_ideal_map (I : Ideal R) :
    ((I.map f).map (algebraMap S (Localization.AtPrime q.asIdeal))) =
      (I.map (algebraMap R (Localization.AtPrime (q.comap f).asIdeal))).map
        (localizationEquiv f q).toRingHom := by
  rw [Ideal.map_map,Ideal.map_map]
  congr 1
  ext r
  exact (localizationEquiv_source f q r).symm
/-- Iterated localization preserves the exact ideal quotient length.
This compares the whole ideal, not merely its support or valuation. -/
theorem length_eq (I : Ideal R) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⧸ (I.map f).map (algebraMap S _)) =
    Module.length (Localization.AtPrime (q.comap f).asIdeal)
      (Localization.AtPrime (q.comap f).asIdeal ⧸ I.map (algebraMap R _)) :=
  (quotient_length (localizationEquiv f q) _ _ (full_ideal_map f q I)).symm
end LocalIdealLengthTransport318
