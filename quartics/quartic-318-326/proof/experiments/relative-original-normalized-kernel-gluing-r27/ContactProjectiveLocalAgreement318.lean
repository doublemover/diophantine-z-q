module
public import ContactProjectiveLocalPresentation318
public section
noncomputable section
namespace ContactProjectiveLocalAgreement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactProjectiveLocalPresentation318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D : Data c n S q) (i j : D.coefficients.Index)
  (T : CommRingCat.{0}) [Algebra ℚ T]
  (f : D.coefficients.ring i →ₐ[ℚ] T) (g : D.coefficients.ring j →ₐ[ℚ] T)
  (h : f.comp (D.coefficients.coefficient i)=g.comp (D.coefficients.coefficient j))
local notation "I" => ContactQuotientChartCoefficient318.extended c (D.chart i) (D.coefficients.ring i) T f n (D.ideal i)
local notation "J" => ContactQuotientChartCoefficient318.extended c (D.chart j) (D.coefficients.ring j) T g n (D.ideal j)
local notation "ki" => ContactQuotientChartCoefficient318.map c (D.chart i) (D.coefficients.ring i) T f n (D.ideal i)
local notation "kj" => ContactQuotientChartCoefficient318.map c (D.chart j) (D.coefficients.ring j) T g n (D.ideal j)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- Any common affine coefficient test sees the SAME original closed
family through both source-chart presentations. -/
lemma agreement : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (localPoint c n S q D i).val=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (localPoint c n S q D j).val := by
  have hi : IsPullback (ki ≫ D.toFamily i) (projectiveInto c (D.chart i) T n I) q
      (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T (f.comp (D.coefficients.coefficient i)) p) := by
    simpa only [RelativeCoefficientFunctorial318.comp] using
      (ContactQuotientOriginalBaseChange318.cartesian c (D.chart i) (D.coefficients.ring i) T f n (D.ideal i)).paste_horiz
        (D.cartesian i)
  have hj : IsPullback (kj ≫ D.toFamily j) (projectiveInto c (D.chart j) T n J) q
      (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T (f.comp (D.coefficients.coefficient i)) p) := by
    rw [h]
    simpa only [RelativeCoefficientFunctorial318.comp] using
      (ContactQuotientOriginalBaseChange318.cartesian c (D.chart j) (D.coefficients.ring j) T g n (D.ideal j)).paste_horiz
        (D.cartesian j)
  let e := hi.isoIsPullback _ _ hj
  have he : e.hom ≫ projectiveInto c (D.chart j) T n J=projectiveInto c (D.chart i) T n I :=
    hi.isoIsPullback_hom_snd hj
  have ha := ContactProjectiveChartAgreement318.agreement c (D.chart i) (D.chart j) T n I J e he
  have hn₁ := ContactProjectiveParameterPoint318.ofIdeal_natural c n (D.coefficients.ring i) T f (D.chart i) (D.ideal i)
  have hn₂ := ContactProjectiveParameterPoint318.ofIdeal_natural c n (D.coefficients.ring j) T g (D.chart j) (D.ideal j)
  exact congrArg Subtype.val (hn₁.symm.trans (ha.trans hn₂))
end ContactProjectiveLocalAgreement318
