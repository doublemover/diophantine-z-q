module
public import ActualGaussianWeberChosenPlaceLift318
public import Mathlib.RingTheory.Ideal.GoingUp
public section
noncomputable section

namespace ActualGaussianWeberIntegralPrimeAbove318

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318

variable {p : ℕ} [Fact p.Prime]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra GaussianInt S]
variable [Algebra.IsIntegral GaussianInt S] [FaithfulSMul GaussianInt S]

/-- At least one genuine height-one prime of the integral extension
lies over the signed Gaussian kernel. The over-place construction
can now be instantiated without assuming a point of a prime fibre. -/
theorem exists_chosen_prime_above (j : ZMod p) (hj : j^2= -1) :
    ∃ w : HeightOneSpectrum S, w.asIdeal.under GaussianInt=selectedIdeal j hj := by
  obtain ⟨Q,hQ,hLo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=S) (selectedIdeal j hj)
  have hU : Q.under GaussianInt=selectedIdeal j hj := hLo.over.symm
  have hQ₀ : Q≠⊥ := by
    intro h
    apply selected_ne_bot j hj
    rw [←hU,h]
    change RingHom.ker (algebraMap GaussianInt S)=⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective GaussianInt S)
  exact ⟨⟨Q,hQ.isPrime,hQ₀⟩,hU⟩

end ActualGaussianWeberIntegralPrimeAbove318
