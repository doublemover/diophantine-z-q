module
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public section
noncomputable section
namespace LocalizedReducedFiber318
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (M : Submonoid A) [IsLocalization M B]

/-- Reducedness of the actual quotient localizes through the actual mapped
ideal. There is no replacement of a base parameter by a rational prime. -/
theorem quotient_reduced (I : Ideal A) [IsReduced (A ⧸ I)] :
    IsReduced (B ⧸ I.map (algebraMap A B)) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  apply Ideal.radical_eq_iff.mp
  rw [← IsLocalization.map_radical M B]
  rw [((Ideal.isRadical_iff_quotient_reduced I).mpr inferInstance).radical]

/-- Principal-ideal localization identifies precisely the quotient required
by the reduced vertical uniformizer argument. -/
theorem parameter_reduced (a : A) [IsReduced (A ⧸ Ideal.span ({a} : Set A))] :
    IsReduced (B ⧸ Ideal.span ({algebraMap A B a} : Set B)) := by
  have h := quotient_reduced (B := B) M (Ideal.span ({a} : Set A))
  simpa only [Ideal.map_span, Set.image_singleton] using h

variable {R : Type*} [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
/-- The same arithmetic base parameter is retained under both structural maps. -/
theorem base_parameter_reduced (r : R)
    [IsReduced (A ⧸ Ideal.span ({algebraMap R A r} : Set A))] :
    IsReduced (B ⧸ Ideal.span ({algebraMap R B r} : Set B)) := by
  have h := parameter_reduced (B := B) M (algebraMap R A r)
  simpa only [← IsScalarTower.algebraMap_apply R A B] using h

end LocalizedReducedFiber318
