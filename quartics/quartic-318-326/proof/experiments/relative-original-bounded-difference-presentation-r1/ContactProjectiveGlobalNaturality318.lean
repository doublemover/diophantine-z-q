module
public import ContactProjectivePresentationPullback318
public section
noncomputable section
namespace ContactProjectiveGlobalNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveLocalPresentation318 ContactProjectiveGlobalClassifyingMap318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) {Z W : Scheme.{0}}
  (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c)
  (r : W ⟶ ContactRelativeLinearOpenChart318.curve T c) [IsClosedImmersion q] [IsClosedImmersion r]
  (h : W ⟶ Z)
  (H : IsPullback h r q (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
    (ContactIntrinsicDifferentials318.structureMap c))) (D : Data c n S q)
local notation "C" => D.coefficients
local notation "E" => ContactProjectivePresentationPullback318.data c n S T φ q r h H D
lemma pulled_point : point c n T r E=ContactProjectiveParameterPoint318.map c n S T φ (point c n S q D) := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (AffineCoefficientCover318.cover ℚ T E.coefficients) _ _
  intro i
  have hn := congrArg Subtype.val (ContactProjectiveParameterPoint318.ofIdeal_natural c n (C.ring i.1)
    (AffineCoefficientPullbackTests318.ring ℚ S T φ C i)
    (AffineCoefficientPullbackTests318.oldHom ℚ S T φ C i) (D.chart i.1) (D.ideal i.1))
  rw [AffineCoefficientPullbackTests318.old_spec] at hn
  change Spec.map (CommRingCat.ofHom (AffineCoefficientPullbackTests318.coefficient ℚ S T φ C i).toRingHom) ≫
      classify c n T r E=_
  rw [local_classify]
  change (ContactProjectiveParameterPoint318.ofIdeal c n _ (D.chart i.1)
    (ContactProjectivePresentationPullbackMaps318.ideal c n S T φ q D i)).val=_
  rw [hn,AffineCoefficientPullbackTests318.coefficient_spec]
  change AffineCoefficientPullbackTests318.toOld ℚ S T φ C i ≫ (localPoint c n S q D i.1).val=
    AffineCoefficientPullbackTests318.toNew ℚ S T φ C i ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ classify c n S q D)
  rw [← local_classify,← Category.assoc,AffineCoefficientPullbackTests318.square,Category.assoc]
/-- Global classification commutes with EVERY actual Cartesian
coefficient change, independently of both local presentation systems. -/
lemma natural (F : Data c n T r) : point c n T r F=
    ContactProjectiveParameterPoint318.map c n S T φ (point c n S q D) :=
  (ContactProjectivePresentationIndependence318.independent c n T r F E).trans
    (pulled_point c n S T φ q r h H D)
end ContactProjectiveGlobalNaturality318
