module
public import ContactProjectiveQuotientGluing318
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public section
noncomputable section
namespace ContactProjectiveQuotientIdealSheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
@[expose] def idealSheaf : (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData :=
  (into R c D).ker
@[expose] def subschemeIso : family R c D ≅ (idealSheaf R c D).subscheme :=
  asIso (into R c D).toImage
@[reassoc] lemma subschemeIso_into : (subschemeIso R c D).hom ≫ (idealSheaf R c D).subschemeι=into R c D :=
  (into R c D).toImage_imageι
private lemma kernel_pullback {X Y Z W : Scheme.{0}} (a : W ⟶ Z) (p : W ⟶ X)
    (m : Z ⟶ Y) (i : X ⟶ Y) [IsClosedImmersion m] (h : IsPullback a p m i) :
    m.ker.comap i=p.ker := by
  have hk := Scheme.Hom.ker_comp_of_isIso h.flip.isoPullback.hom (pullback.fst i m)
  rw [h.flip.isoPullback_hom_fst] at hk
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion m i).symm.trans hk.symm
/-- The global WHOLE ideal restricts to the original full finite-chart
quotient ideal sheaf, without radicalization or loss at infinity. -/
lemma finite_restriction : (idealSheaf R c D).comap
    (ContactOriginalRelativePolynomialCharts318.finiteInto R c)=
    (finiteInto R c D).ker :=
  kernel_pullback _ _ _ _ (finite_square R c D)
lemma infinity_restriction : (idealSheaf R c D).comap
    (ContactOriginalRelativePolynomialCharts318.infinityInto R c)=
    (infinityInto R c D).ker :=
  kernel_pullback _ _ _ _ (infinity_square R c D)
end ContactProjectiveQuotientIdealSheaf318
