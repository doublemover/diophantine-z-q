module
public import ActualFTRayOrderedClassTags318
public import ActualChebVonMangoldt318
public section
noncomputable section
namespace ActualFTFrobeniusWeight318

open ActualFTRayIndexTwo318 ActualFTRayOrderedClassTags318
open ActualChebVonMangoldt318 ActualAffineChebClassUnion318 ArithmeticFunction

variable {A G J : Type*} [CommGroup A] [Group G] [DecidableEq J]
  {σ : A →* A} (P : Presentation (G := G) σ) (g : J → A)

/-- Exactly FT (1.9), once F is a chosen Frobenius at unramified
rational primes (and none on ramified primes). The base is minFac,
not the Frobenius of a prime power or a chosen Gaussian factor. -/
def weight (F : ℕ → Option G) (j : J) (n : ℕ) : ℝ := by
  classical
  exact if (∃ x : G, F n.minFac=some x ∧
    (∃ t : G, t * P.incl (g j) * t⁻¹=x)) then vonMangoldt n else 0

theorem weight_exact (HI : Function.Injective g) (HS : ∀ a b, g a ≠ σ (g b))
    (F : ℕ → Option G) (j : J) (n : ℕ) :
    classMangoldt (select P g F) j n = weight P g F j n := by
  classical
  unfold classMangoldt part weight
  by_cases H : ∃ x : G, F n.minFac=some x ∧ (∃ t : G, t * P.incl (g j) * t⁻¹=x)
  · have h := (select_eq_some P g HI HS F n.minFac j).mpr H
    rw [if_pos h,if_pos H]
  · have h : select P g F n.minFac ≠ some j :=
      fun hh => H ((select_eq_some P g HI HS F n.minFac j).mp hh)
    rw [if_neg h,if_neg H]

end ActualFTFrobeniusWeight318
