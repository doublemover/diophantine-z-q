module
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public section
noncomputable section
namespace LocalQuotientLengthSupport318
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R]
/-- Full original quotient-image criterion at EVERY prime. -/
lemma quotient_image (I : Ideal R) (p : PrimeSpectrum R) :
    p ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔ I ≤ p.asIdeal := by
  change p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ↔ _
  rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,Ideal.mk_ker]
  exact PrimeSpectrum.mem_zeroLocus p I
/-- Away from its full quotient image, the actual localized ideal is
unit: a literal member outside the prime maps to a genuine unit. -/
lemma localization_top (I : Ideal R) (p : PrimeSpectrum R) (h : ¬I ≤ p.asIdeal) :
    I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤ := by
  classical
  obtain ⟨a,ha,hp⟩ : ∃ a ∈ I, a ∉ p.asIdeal := by
    by_contra hn
    apply h
    intro a ha
    by_contra hp
    exact hn ⟨a,ha,hp⟩
  exact (I.map (algebraMap R (Localization.AtPrime p.asIdeal))).eq_top_of_isUnit_mem
    (Ideal.mem_map_of_mem _ ha) (IsLocalization.map_units (Localization.AtPrime p.asIdeal) (⟨a,hp⟩ : p.asIdeal.primeCompl))
lemma length_zero (I : Ideal R) (p : PrimeSpectrum R) (h : ¬I ≤ p.asIdeal) :
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R _)) = 0 := by
  rw [localization_top I p h]
  exact Module.length_eq_zero _ _
end LocalQuotientLengthSupport318
