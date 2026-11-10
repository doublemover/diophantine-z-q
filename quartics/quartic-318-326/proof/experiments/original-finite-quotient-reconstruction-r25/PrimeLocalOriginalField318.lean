module
public import HeightOneDVR318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace PrimeLocalOriginalField318
variable (B L : Type*) [CommRing B] [IsDomain B] [Field L]
  [Algebra B L] [IsFractionRing B L] (P : Ideal B) [P.IsPrime]

/-- The actual prime localization, not an abstract isomorphic DVR. -/
abbrev Local := Localization.AtPrime P

lemma denominator_unit (s : P.primeCompl) : IsUnit (algebraMap B L s) := by
  apply IsUnit.mk0
  have hs : (s:B) ≠ 0 := by
    intro hz
    apply s.property
    simpa only [hz] using P.zero_mem
  simpa only [map_zero] using (IsFractionRing.injective B L).ne hs

/-- Extend the original affine generic embedding to its original local ring. -/
@[expose] def embedding : Local B P →+* L :=
  IsLocalization.lift (denominator_unit B L P)

lemma embedding_integral (b : B) :
    embedding B L P (algebraMap B (Local B P) b) = algebraMap B L b :=
  IsLocalization.lift_eq (denominator_unit B L P) b

@[expose] def originalAlgebra : Algebra (Local B P) L :=
  (embedding B L P).toAlgebra

local instance : Algebra (Local B P) L := originalAlgebra B L P

instance originalTower : IsScalarTower B (Local B P) L :=
  IsScalarTower.of_algebraMap_eq (fun b => (embedding_integral B L P b).symm)

/-- The SAME field is the fraction field of this actual prime localization. -/
theorem fraction : IsFractionRing (Local B P) L :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl (Local B P) L

lemma embedding_injective : Function.Injective (embedding B L P) := by
  letI := fraction B L P
  exact IsFractionRing.injective (Local B P) L
end PrimeLocalOriginalField318
