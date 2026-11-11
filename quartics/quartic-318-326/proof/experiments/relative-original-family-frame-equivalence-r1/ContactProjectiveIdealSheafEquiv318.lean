module
public import ContactProjectiveDatumRecovery318
public import AffineClosedRestrictionIso318
public section
noncomputable section
namespace ContactProjectiveIdealSheafEquiv318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
private lemma datum_ext {D E : Datum R c} (hf : D.finiteIdeal=E.finiteIdeal)
    (hi : D.infinityIdeal=E.infinityIdeal) : D=E := by
  cases D
  cases E
  simp_all
lemma datum_iso {Z W : Scheme.{0}}
    (p : Z ⟶ ContactOriginalRelativePolynomialCharts318.curve R c)
    (q : W ⟶ ContactOriginalRelativePolynomialCharts318.curve R c)
    [IsClosedImmersion p] [IsClosedImmersion q] (e : Z ≅ W) (he : e.hom ≫ q=p) :
    ContactProjectiveClosedData318.datum R c p=ContactProjectiveClosedData318.datum R c q := by
  apply datum_ext R c
  · exact AffineClosedRestrictionIso318.ideal_eq p q e he (finiteRing R c)
      (ContactOriginalRelativePolynomialCharts318.finiteInto R c)
  · exact AffineClosedRestrictionIso318.ideal_eq p q e he (infinityRing R c)
      (ContactOriginalRelativePolynomialCharts318.infinityInto R c)
@[expose] def toIdeal : Datum R c → (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData :=
  ContactProjectiveQuotientIdealSheaf318.idealSheaf R c
@[expose] def fromIdeal (I : (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData) : Datum R c :=
  ContactProjectiveClosedData318.datum R c I.subschemeι
lemma to_from (I : (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData) :
    toIdeal R c (fromIdeal R c I)=I :=
  (ContactProjectiveClosedRecovery318.idealSheaf_eq R c I.subschemeι).trans I.ker_subschemeι
lemma from_to (D : Datum R c) : fromIdeal R c (toIdeal R c D)=D := by
  have h := datum_iso R c (ContactProjectiveQuotientGluing318.into R c D)
    (toIdeal R c D).subschemeι (ContactProjectiveQuotientIdealSheaf318.subschemeIso R c D)
    (ContactProjectiveQuotientIdealSheaf318.subschemeIso_into R c D)
  exact h.symm.trans (ContactProjectiveDatumRecovery318.datum R c D)
/-- A genuine two-sided classification of ALL ideal sheaves on the
actual projective source by compatible full affine chart ideals.
This is descent of closed quotients, NOT representation of their moduli
functor or identification of the Picard/Jacobian space. -/
@[expose] def equivalence : Datum R c ≃ (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData where
  toFun := toIdeal R c
  invFun := fromIdeal R c
  left_inv := from_to R c
  right_inv := to_from R c
end ContactProjectiveIdealSheafEquiv318
