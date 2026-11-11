module
public import CanonicalStalkModule318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public section
noncomputable section
namespace AffineTildeQuotientStalk318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
@[expose] abbrev LocalRing := (Spec (CommRingCat.of R)).presheaf.stalk p
@[expose] abbrev QuotientSheaf :=
  tilde (R := CommRingCat.of R) (ModuleCat.of R (R ⧸ I))
/-- The full original ideal mapped to the ACTUAL structure-sheaf stalk. -/
@[expose] def localIdeal : Ideal (LocalRing R p) :=
  I.map (algebraMap R (LocalRing R p))
lemma localized_ideal :
    I.localized' (LocalRing R p) p.asIdeal.primeCompl
      (Algebra.linearMap R (LocalRing R p)) = localIdeal R I p := by
  rw [Submodule.localized'_eq_span]
  rfl
/-- The canonical localization comparison is first constructed over R,
then extended over the EXISTING canonical local-ring actions. It does
not install a substitute module action on the sheaf stalk. -/
@[expose] def iso :
    CanonicalStalkModule318.stalk (QuotientSheaf R I) p ≃ₗ[LocalRing R p]
      LocalRing R p ⧸ localIdeal R I p := by
  let e := IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (tilde.toStalk (R := CommRingCat.of R) (ModuleCat.of R (R ⧸ I)) p).hom
    (I.toLocalizedQuotient' (LocalRing R p) p.asIdeal.primeCompl
      (Algebra.linearMap R (LocalRing R p)))
  exact (e.extendScalarsOfIsLocalization p.asIdeal.primeCompl (LocalRing R p)).trans
    (Submodule.quotEquivOfEq _ _ (localized_ideal R I p))
/-- The length is that of the actual tilde stalk over the actual
structure-sheaf local ring, not length of an independently chosen module. -/
theorem length_eq :
    Module.length (LocalRing R p) (CanonicalStalkModule318.stalk (QuotientSheaf R I) p) =
      Module.length (LocalRing R p) (LocalRing R p ⧸ localIdeal R I p) :=
  (iso R I p).length_eq
end AffineTildeQuotientStalk318
