module
public import ContactRadical318
public import ContactProjectiveModel318

@[expose] public section
noncomputable section

namespace OriginalLiteralContactQuotientPoint318
open AlgebraicGeometry CategoryTheory Polynomial
open ContactKummerOrder318 (R OpenBase denominator)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The quotient's actual projective coordinate is T=32s. The old
homogeneous five forms use s, including the value at infinity. -/
def coord (u v : ℤ) : ℚ := 32*((u:ℚ)/(v:ℚ))

theorem actual_noncontact (u v : ℤ) (hne : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0) :
    v≠0 ∧ ∀ i : Fin 4, coord u v ≠ LinearContactSquareclass318.contacts i := by
  have hv : v ≠ 0 := by simpa [ContactRadical318.forms] using hne 0
  have hu : u ≠ 0 := by simpa [ContactRadical318.forms] using hne 1
  have h₁ : u-v ≠ 0 := by simpa [ContactRadical318.forms] using hne 2
  have h₂ : u-2401*v ≠ 0 := by simpa [ContactRadical318.forms] using hne 3
  have h₃ : 32*u+343*v ≠ 0 := by simpa [ContactRadical318.forms] using hne 4
  have hvQ : (v:ℚ) ≠ 0 := by exact_mod_cast hv
  refine ⟨hv,?_⟩
  intro i hi
  have h : 32*(u:ℚ) = LinearContactSquareclass318.contacts i * (v:ℚ) := by
    apply (div_eq_iff hvQ).mp
    simpa only [coord,mul_div_assoc] using hi
  fin_cases i
  · simp [LinearContactSquareclass318.contacts] at h
    apply hu
    exact_mod_cast h
  · norm_num [LinearContactSquareclass318.contacts] at h
    have hz : (u:ℚ)-(v:ℚ)=0 := by linarith
    exact h₁ (by exact_mod_cast hz)
  · norm_num [LinearContactSquareclass318.contacts] at h
    have hz : (u:ℚ)-2401*(v:ℚ)=0 := by linarith
    exact h₂ (by exact_mod_cast hz)
  · norm_num [LinearContactSquareclass318.contacts] at h
    have hz : 32*(u:ℚ)+343*(v:ℚ)=0 := by linarith
    exact h₃ (by exact_mod_cast hz)

/-- The source is the literal finite chart's actual polynomial ring,
not a newly introduced copy of the normalized quotient. -/
def evalAffine (u v : ℤ) : R →ₐ[ℚ] ℚ := Polynomial.aeval (coord u v)

variable (u v : ℤ) (hne : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0)

private theorem denominator_unit : IsUnit (evalAffine u v denominator) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [evalAffine,aeval_def,algebraMap_self,eval₂_id] using
    (ContactKummerCover318.omitted_points (coord u v)).mpr (actual_noncontact u v hne).2

/-- Evaluate the entire canonical contact localization at the given
noncontact rational pair. No chart or complex lift is an input. -/
def evalOpen : OpenBase →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom denominator (denominator_unit u v hne)

theorem evalOpen_finite (a : R) :
    evalOpen u v hne (algebraMap R OpenBase a) = evalAffine u v a :=
  IsLocalization.Away.lift_eq denominator (denominator_unit u v hne) a

theorem evalOpen_t : evalOpen u v hne (algebraMap R OpenBase X) = coord u v :=
  (evalOpen_finite u v hne X).trans (aeval_X (coord u v))

def affinePoint : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (evalAffine u v).toRingHom)

def openPoint : Spec (CommRingCat.of ℚ) ⟶ ContactKummerCover318.base :=
  Spec.map (CommRingCat.ofHom (evalOpen u v hne).toRingHom)

/-- This is the one point on the actual projective quotient chart
carrying the literal arithmetic coordinate (including the factor 32). -/
def point : Spec (CommRingCat.of ℚ) ⟶ ProjectiveJLine318.scheme ℚ :=
  affinePoint u v ≫ JLineAtlas318.chart ℚ 1

theorem openPoint_over : openPoint u v hne ≫ ContactKummerCover318.baseMap = affinePoint u v := by
  unfold affinePoint openPoint ContactKummerCover318.baseMap
  rw [←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact evalOpen_finite u v hne

theorem openPoint_is_original : openPoint u v hne ≫ ContactProjectiveModel318.baseOpen =
    point u v := by
  change openPoint u v hne ≫ (ContactKummerCover318.baseMap ≫ JLineAtlas318.chart ℚ 1) =
    affinePoint u v ≫ JLineAtlas318.chart ℚ 1
  rw [←Category.assoc,openPoint_over]

end OriginalLiteralContactQuotientPoint318

#print axioms OriginalLiteralContactQuotientPoint318.actual_noncontact
#print axioms OriginalLiteralContactQuotientPoint318.evalOpen_finite
#print axioms OriginalLiteralContactQuotientPoint318.evalOpen_t
#print axioms OriginalLiteralContactQuotientPoint318.openPoint_over
#print axioms OriginalLiteralContactQuotientPoint318.openPoint_is_original
