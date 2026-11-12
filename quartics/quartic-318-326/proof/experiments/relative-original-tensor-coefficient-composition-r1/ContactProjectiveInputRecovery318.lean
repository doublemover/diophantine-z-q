module
public import SchemeClosedFamilyCoverComparison318
public section
noncomputable section
namespace ContactProjectiveInputRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveLocalPresentation318 ContactProjectiveGlobalClassifyingMap318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D : Data c n S q)
local notation "x" => point c n S q D
local notation "r" => ContactProjectivePointFamily318.into c n S x
local notation "p" => ContactRelativeLinearOpenChart318.projection S c
local notation "C" => D.coefficients
local notation "U" => AffineCoefficientCover318.cover ℚ S C
variable (i : C.Index)
abbrev modelMap : ContactQuotientChart318.family c (D.chart i) (C.ring i) n (D.ideal i) ⟶
    ContactProjectivePointFamily318.family c n S x :=
  ContactProjectivePointLocalModel318.map c n S (C.ring i) x (C.coefficient i) (D.chart i) (D.ideal i)
    (local_classify c n S q D i).symm
lemma left_cartesian : IsPullback (D.toFamily i)
    (ContactQuotientChart318.projection c (D.chart i) (C.ring i) n (D.ideal i)) (q ≫ p) (U.f i) := by
  have h := (D.cartesian i).paste_vert
    (RelativeCoefficientCartesian318.cartesian (CommRingCat.of ℚ) S (C.ring i) (C.coefficient i)
      (ContactIntrinsicDifferentials318.structureMap c))
  simpa only [ContactAffineQuotientToProjective318.into_projection] using h
lemma right_cartesian : IsPullback (modelMap c n S q D i)
    (ContactQuotientChart318.projection c (D.chart i) (C.ring i) n (D.ideal i)) (r ≫ p) (U.f i) := by
  have h := (ContactProjectivePointLocalModel318.cartesian c n S (C.ring i) x (C.coefficient i)
    (D.chart i) (D.ideal i) (local_classify c n S q D i).symm).paste_vert
      (RelativeCoefficientCartesian318.cartesian (CommRingCat.of ℚ) S (C.ring i) (C.coefficient i)
        (ContactIntrinsicDifferentials318.structureMap c))
  simpa only [ContactAffineQuotientToProjective318.into_projection] using h
lemma model_source : D.toFamily i ≫ q=modelMap c n S q D i ≫ r :=
  (D.cartesian i).w.trans (ContactProjectivePointLocalModel318.source c n S (C.ring i) x
    (C.coefficient i) (D.chart i) (D.ideal i) (local_classify c n S q D i).symm).symm
@[expose] def localIso : pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i) :=
  (left_cartesian c n S q D i).isoPullback.symm ≪≫ (right_cartesian c n S q D i).isoPullback
lemma localIso_source : (localIso c n S q D i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
    pullback.fst (q ≫ p) (U.f i) ≫ q := by
  simp only [localIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    (right_cartesian c n S q D i).isoPullback_hom_fst]
  rw [← model_source,← Category.assoc,(left_cartesian c n S q D i).isoPullback_inv_fst]
/-- Every independently presented original closed family is recovered
by the ACTUAL global universal family over its global classifying point. -/
@[expose] def comparison : Z ≅ ContactProjectivePointFamily318.family c n S x :=
  SchemeClosedFamilyCoverComparison318.iso p q r U (localIso c n S q D) (localIso_source c n S q D)
@[reassoc] lemma comparison_source : (comparison c n S q D).hom ≫ r=q :=
  SchemeClosedFamilyCoverComparison318.iso_into _ _ _ _ _ _
lemma ideal_recovery : ContactProjectivePointFamily318.idealSheaf c n S x=q.ker := by
  have h := Scheme.Hom.ker_comp_of_isIso (comparison c n S q D).hom r
  have he := congrArg (fun f : Z ⟶ ContactRelativeLinearOpenChart318.curve S c => f.ker)
    (comparison_source c n S q D)
  exact h.symm.trans he
end ContactProjectiveInputRecovery318
