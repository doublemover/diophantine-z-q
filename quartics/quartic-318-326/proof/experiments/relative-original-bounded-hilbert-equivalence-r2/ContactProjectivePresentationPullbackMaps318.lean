module
public import ContactProjectivePresentationIso318
public import AffineCoefficientPullbackTests318
public section
noncomputable section
namespace ContactProjectivePresentationPullbackMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactProjectiveLocalPresentation318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) {Z W : Scheme.{0}}
  (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c)
  (r : W ⟶ ContactRelativeLinearOpenChart318.curve T c) [IsClosedImmersion q] [IsClosedImmersion r]
  (h : W ⟶ Z)
  (H : IsPullback h r q (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
    (ContactIntrinsicDifferentials318.structureMap c))) (D : Data c n S q)
local notation "C" => D.coefficients
variable (i : AffineCoefficientPullbackTests318.index ℚ S T φ C)
local notation "L" => AffineCoefficientPullbackTests318.ring ℚ S T φ C i
local notation "γ" => AffineCoefficientPullbackTests318.oldHom ℚ S T φ C i
local notation "δ" => AffineCoefficientPullbackTests318.coefficient ℚ S T φ C i
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ p
local notation "α" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) T L δ p
local notation "β" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) (C.ring i.1) L γ p
local notation "old" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S (C.ring i.1) (C.coefficient i.1) p
abbrev ideal : Ideal c (D.chart i.1) L n := ContactQuotientChartCoefficient318.extended c (D.chart i.1)
  (C.ring i.1) L γ n (D.ideal i.1)
local notation "Q" => family c (D.chart i.1) L n (ideal c n S T φ q D i)
local notation "qi" => projectiveInto c (D.chart i.1) L n (ideal c n S T φ q D i)
local notation "κ" => ContactQuotientChartCoefficient318.map c (D.chart i.1) (C.ring i.1) L γ n (D.ideal i.1)
lemma curve_square : β ≫ old=α ≫ b := by
  rw [RelativeCoefficientFunctorial318.comp,RelativeCoefficientFunctorial318.comp,
    AffineCoefficientPullbackTests318.hom_comp]
lemma total_cartesian : IsPullback (κ ≫ D.toFamily i.1) qi q (α ≫ b) := by
  rw [← curve_square c n S T φ q D i]
  exact (ContactQuotientOriginalBaseChange318.cartesian c (D.chart i.1) (C.ring i.1) L γ n (D.ideal i.1)).paste_horiz
    (D.cartesian i.1)
@[expose] def toPullback : Q ⟶ pullback q b :=
  pullback.lift (κ ≫ D.toFamily i.1) (qi ≫ α)
    (by simpa only [Category.assoc] using (total_cartesian c n S T φ q D i).w)
/-- The actual new local family map is constructed through the given
whole original Cartesian family, not chosen from a point comparison. -/
@[expose] def toFamily : Q ⟶ W := toPullback c n S T φ q D i ≫ H.isoPullback.inv
@[reassoc] lemma toFamily_source : toFamily c n S T φ q r h H D i ≫ r=qi ≫ α := by
  rw [toFamily,Category.assoc,H.isoPullback_inv_snd]
  exact pullback.lift_snd _ _ _
@[reassoc] lemma toFamily_old : toFamily c n S T φ q r h H D i ≫ h=κ ≫ D.toFamily i.1 := by
  rw [toFamily,Category.assoc,H.isoPullback_inv_fst]
  exact pullback.lift_fst _ _ _
lemma cartesian : IsPullback (toFamily c n S T φ q r h H D i) qi r α := by
  apply IsPullback.of_right (h₁₂ := h) (h₂₂ := b)
  · rw [toFamily_old]
    exact total_cartesian c n S T φ q D i
  · exact toFamily_source c n S T φ q r h H D i
  · exact H
end ContactProjectivePresentationPullbackMaps318
