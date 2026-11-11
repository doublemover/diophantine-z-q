module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace FiniteAlgebraSpectrumBound318
open scoped BigOperators
universe u v
variable (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C] [Module.Finite K C]
/-- The number of points of a finite algebra is at most its vector-space
rank, including nilpotents and non-algebraically-closed fields. -/
lemma card_spectrum_le : Nat.card (PrimeSpectrum C)≤Module.finrank K C := by
  classical
  letI : IsArtinianRing C := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum C) := Fintype.ofFinite _
  have hcoprime : Pairwise (fun p q : PrimeSpectrum C => IsCoprime p.asIdeal q.asIdeal) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (fun he => hpq (PrimeSpectrum.ext he))
  let ev : C →ₗ[K] (∀ p : PrimeSpectrum C, C ⧸ p.asIdeal) :=
    LinearMap.pi fun p => (Ideal.Quotient.mkₐ K p.asIdeal).toLinearMap
  have hs : Function.Surjective ev := by
    intro z
    obtain ⟨c,hc⟩ := Ideal.pi_quotient_surjective hcoprime z
    exact ⟨c,funext hc⟩
  have hp (p : PrimeSpectrum C) : 1≤Module.finrank K (C ⧸ p.asIdeal) :=
    (Module.finrank_pos_iff_of_free K (C ⧸ p.asIdeal)).mpr inferInstance
  calc
    Nat.card (PrimeSpectrum C) = ∑ _p : PrimeSpectrum C, 1 := by simp
    _ ≤ ∑ p : PrimeSpectrum C, Module.finrank K (C ⧸ p.asIdeal) :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = Module.finrank K (∀ p : PrimeSpectrum C, C ⧸ p.asIdeal) :=
      (Module.finrank_pi_fintype K).symm
    _ ≤ Module.finrank K C := LinearMap.finrank_le_finrank_of_surjective hs
end FiniteAlgebraSpectrumBound318
