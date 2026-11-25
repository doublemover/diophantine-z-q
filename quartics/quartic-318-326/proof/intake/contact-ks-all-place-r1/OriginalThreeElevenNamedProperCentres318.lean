module

public import OriginalFineArithmeticPlaceSwitch318
public import OriginalGoodTraitProperFineCentre318
public import OriginalRetainedComplexZeroByPasting318
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace OriginalThreeElevenNamedProperCentres318

open AlgebraicGeometry CategoryTheory
open IsDedekindDomain
open OriginalFineArithmeticPlaceSwitch318
open OriginalRetainedComplexZeroByPasting318 (specOf spec_comp)
open scoped nonZeroDivisors

universe u
abbrev FullBase := Localization.Away (33:ℤ)

theorem denominator_divides (n : Lane) : denominator n ∣ (33:ℤ) := by
  cases n <;> decide

def baseForget (n : Lane) : IntegerBase n→+* FullBase :=
  IsLocalization.Away.lift (denominator n) (g:=algebraMap ℤ FullBase)
    (IsLocalization.Away.isUnit_of_dvd (S:=FullBase) (denominator_divides n))

variable {E : Type u} [Field E] [CharZero E]

def oldFullBase : FullBase→+*E :=
  IsLocalization.Away.lift (33:ℤ) (g:=Int.castRingHom E)
    (isUnit_iff_ne_zero.2 (by norm_num : (33:E)≠0))

theorem full_base_reads_lower (n : Lane) :
    (oldFullBase (E:=E)).comp (baseForget n)=oldFieldBase (E:=E) n := by
  apply IsLocalization.ringHom_ext (.powers (denominator n))
  ext z
  change oldFullBase (E:=E) (baseForget n (algebraMap ℤ (IntegerBase n) z))=
    oldFieldBase (E:=E) n (algebraMap ℤ (IntegerBase n) z)
  simp only [baseForget, oldFullBase, oldFieldBase, IsLocalization.Away.lift_eq, map_intCast]

/-- Exact base geometry required from the represented original PEL
functors. The two maps here are the actual full-mark forgets,
not morphisms selected by matching the numbers T or χ. -/
structure OriginalFineBases where
  lower : Lane→Scheme.{u}
  full : Scheme.{u}
  p : ∀ n, lower n ⟶ Spec (CommRingCat.of (IntegerBase n))
  pFull : full ⟶ Spec (CommRingCat.of FullBase)
  proper : ∀ n, IsProper (p n)
  properFull : IsProper pFull
  forget : ∀ n, full ⟶ lower n
  forget_over : ∀ n, forget n ≫ p n = pFull ≫ specOf (baseForget n)

/-- This is one retained point, with both lower marks obtained by
exact composition. Its field is not part of the integral choices. -/
structure CommonMark (B : OriginalFineBases.{u}) where
  P33 : Spec (CommRingCat.of E) ⟶ B.full
  over : P33 ≫ B.pFull=specOf (oldFullBase (E:=E))

variable (B : OriginalFineBases.{u}) (m : CommonMark (E:=E) B)

abbrev lowerMark (n : Lane) : Spec (CommRingCat.of E) ⟶ B.lower n :=
  m.P33 ≫ B.forget n

theorem lower_mark_over (n : Lane) :
    lowerMark B m n ≫ B.p n=specOf (oldFieldBase (E:=E) n) := by
  change (m.P33 ≫ B.forget n) ≫ B.p n=_
  calc
    _ = m.P33 ≫ (B.forget n ≫ B.p n) := Category.assoc _ _ _
    _ = (m.P33 ≫ B.pFull) ≫ specOf (baseForget n) := by
      rw [B.forget_over,Category.assoc]
    _ = _ := by rw [m.over,spec_comp,full_base_reads_lower]

variable {O : Type u} [CommRing O] [IsDomain O] [IsDedekindDomain O]
  [Algebra O E] [IsFractionRing O E] (w : HeightOneSpectrum O)

abbrev actualFieldInclusion :
    Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (localInt (E:=E) w)) :=
  OriginalGoodTraitProperFineCentre318.generic

theorem valuative_square :
    lowerMark B m (selected w) ≫ B.p (selected w)=
      actualFieldInclusion (E:=E) w ≫ specOf (actualBase (E:=E) w) := by
  rw [lower_mark_over]
  change _=specOf (algebraMap (localInt (E:=E) w) E) ≫ specOf (actualBase (E:=E) w)
  rw [spec_comp,keeps_generic_base]

def namedCentre : Spec (CommRingCat.of (localInt (E:=E) w)) ⟶ B.lower (selected w) :=
  letI := B.proper (selected w)
  OriginalGoodTraitProperFineCentre318.centre (B.p (selected w))
    (lowerMark B m (selected w)) (specOf (actualBase (E:=E) w)) (valuative_square B m w)

theorem named_centre_retains :
    actualFieldInclusion (E:=E) w ≫ namedCentre B m w=m.P33 ≫ B.forget (selected w) := by
  letI := B.proper (selected w)
  exact OriginalGoodTraitProperFineCentre318.centre_generic (B.p (selected w))
    (lowerMark B m (selected w)) (specOf (actualBase (E:=E) w)) (valuative_square B m w)

theorem named_centre_over :
    namedCentre B m w ≫ B.p (selected w)=specOf (actualBase (E:=E) w) := by
  letI := B.proper (selected w)
  exact OriginalGoodTraitProperFineCentre318.centre_over (B.p (selected w))
    (lowerMark B m (selected w)) (specOf (actualBase (E:=E) w)) (valuative_square B m w)

theorem named_centre_unique (x : Spec (CommRingCat.of (localInt (E:=E) w)) ⟶ B.lower (selected w))
    (over : x ≫ B.p (selected w)=specOf (actualBase (E:=E) w))
    (same : actualFieldInclusion (E:=E) w ≫ x=m.P33 ≫ B.forget (selected w)) :
    x=namedCentre B m w := by
  letI := B.proper (selected w)
  exact OriginalGoodTraitProperFineCentre318.centre_unique (B.p (selected w))
    (lowerMark B m (selected w)) (specOf (actualBase (E:=E) w)) (valuative_square B m w)
    x over same

end OriginalThreeElevenNamedProperCentres318
