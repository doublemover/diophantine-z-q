module
public import ActualGaussianWeberIntegerGaloisGroup318
public import Mathlib.RingTheory.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberCanonicalRingFrob318

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberIntegerGaloisGroup318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L]
variable [hFinite : FiniteDimensional Base L] [hGalois : IsGalois Base L]

include hFinite hGalois in
theorem gal_finite : Finite (L≃ₐ[Base]L) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [IsGalois.card_aut_eq_finrank]
  exact Module.finrank_pos.ne'

/-- Use the true ring Galois group on the literal integral embedding
to construct stock arithmetic Frobenius on the actual number field. -/
@[expose] def arithAt (w : HeightOneSpectrum (𝓞 L)) : L≃ₐ[Base]L := by
  letI := integralAlgebra (algebraMap Base L)
  letI : IsGaloisGroup (L≃ₐ[Base]L) GaussianInt (𝓞 L) := gaussian_galois_group L
  letI : SMulCommClass (L≃ₐ[Base]L) GaussianInt (𝓞 L) :=
    (gaussian_galois_group L).commutes
  letI : Algebra.IsInvariant GaussianInt (𝓞 L) (L≃ₐ[Base]L) :=
    (gaussian_galois_group L).isInvariant
  letI := gal_finite L
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  exact arithFrobAt GaussianInt (L≃ₐ[Base]L) w.asIdeal

theorem arithmetic_exponent (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) :
    letI := integralAlgebra (algebraMap Base L)
    (arithAt L w) • x - x^(Nat.card (GaussianInt ⧸ w.asIdeal.under GaussianInt)) ∈ w.asIdeal := by
  letI := integralAlgebra (algebraMap Base L)
  letI : SMulCommClass (L≃ₐ[Base]L) GaussianInt (𝓞 L) :=
    (gaussian_galois_group L).commutes
  letI : Algebra.IsInvariant GaussianInt (𝓞 L) (L≃ₐ[Base]L) :=
    (gaussian_galois_group L).isInvariant
  letI := gal_finite L
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  unfold arithAt
  exact (IsArithFrobAt.arithFrobAt GaussianInt (L≃ₐ[Base]L) w.asIdeal) x

variable {p : ℕ} [Fact p.Prime]

/-- The arithmetic exponent is literally the original rational p
at its selected signed degree-one Gaussian contraction. -/
theorem chosen_signed_exponent (w : HeightOneSpectrum (𝓞 L))
    (j : ZMod p) (hj : j^2= -1)
    (hUnder : letI := integralAlgebra (algebraMap Base L)
      w.asIdeal.under GaussianInt=selectedIdeal j hj) (x : 𝓞 L) :
    (arithAt L w) • x-x^p ∈ w.asIdeal := by
  letI := integralAlgebra (algebraMap Base L)
  have hp : Nat.card (GaussianInt ⧸ w.asIdeal.under GaussianInt)=p := contracted_card w j hj hUnder
  have hx := arithmetic_exponent L w x
  rw [hp] at hx
  exact hx

theorem chosen_actual_field_action (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) :
    algebraMap (𝓞 L) L ((arithAt L w) • x)=arithAt L w (algebraMap (𝓞 L) L x) :=
  rfl

end ActualGaussianWeberCanonicalRingFrob318
