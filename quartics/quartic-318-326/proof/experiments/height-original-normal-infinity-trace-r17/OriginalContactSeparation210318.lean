module
public import IntegralSourceBranches318
public section
noncomputable section
namespace OriginalContactSeparation210318
/-- Exact arithmetic certificate for all six original contact differences.
The only possible contact-collision rational primes are2,3,5,7. -/
lemma difference_divides (i j : Fin 4) (h : i≠j) :
    IntegralSourceBranches318.contacts ℤ i-IntegralSourceBranches318.contacts ℤ j ∣ (210:ℤ)^10 := by
  fin_cases i <;> fin_cases j <;> norm_num [IntegralSourceBranches318.contacts] at h ⊢
variable (R : Type*) [CommRing R]
lemma contacts_cast (i : Fin 4) : (Int.castRingHom R) (IntegralSourceBranches318.contacts ℤ i)=
    IntegralSourceBranches318.contacts R i := by
  fin_cases i <;> norm_num [IntegralSourceBranches318.contacts]
lemma two_unit (h : IsUnit (210:R)) : IsUnit (2:R) :=
  isUnit_of_dvd_unit (show (2:R)∣210 from ⟨105,by norm_num⟩) h
lemma contacts_separated (h : IsUnit (210:R)) (i j : Fin 4) (hij : i≠j) :
    IsUnit (IntegralSourceBranches318.contacts R i-IntegralSourceBranches318.contacts R j) := by
  have hd := map_dvd (Int.castRingHom R) (difference_divides i j hij)
  have hp : (Int.castRingHom R) ((210:ℤ)^10)=(210:R)^10 := by norm_num
  rw [map_sub,contacts_cast,contacts_cast,hp] at hd
  exact isUnit_of_dvd_unit hd (h.pow 10)
end OriginalContactSeparation210318
