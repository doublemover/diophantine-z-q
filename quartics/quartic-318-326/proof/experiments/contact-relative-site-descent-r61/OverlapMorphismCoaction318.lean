module
public import OriginalGeometricAffineLine318
public section
noncomputable section
namespace OverlapMorphismCoaction318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
open AffineModuleBaseChange318 AffineOverlapCoaction318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]

/-- An actual module-overlap intertwiner is exactly compatible with the
candidate coactions obtained by the original adjunction/tensor comparison. -/
lemma module_coaction {N M : ModuleCat S} (h : N ⟶ M)
    (a : first R S N ⟶ second R S N) (b : first R S M ⟶ second R S M)
    (hab : a ≫ (ModuleCat.extendScalars (rightMap R S S).hom).map h =
      (ModuleCat.extendScalars (leftMap R S S).hom).map h ≫ b) :
    homEquiv R S N a ≫ (pullPush R S S).map h = h ≫ homEquiv R S M b := by
  have hm : (ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv N (second R S N) a ≫
      (pushPull R S S).map h =
      h ≫ (ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv M (second R S M) b :=
    ((ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv_naturality_left_square
      h b a ((ModuleCat.extendScalars (rightMap R S S).hom).map h) hab.symm).symm
  rw [homEquiv_apply, homEquiv_apply, Category.assoc]
  change _ ≫ ((naturalIso R S S).hom.app N ≫ (pullPush R S S).map h) = _
  rw [← (naturalIso R S S).hom.naturality h, ← Category.assoc, hm, Category.assoc]
  rfl

/-- Opaque categorical transport of a genuine commutative square through
its four fixed endpoint comparisons. -/
private lemma conjugate_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B A' B' : C} {X Y X' Y' : D}
    (s : X ≅ F.obj A) (t : Y ≅ F.obj B)
    (s' : X' ≅ F.obj A') (t' : Y' ≅ F.obj B')
    (a : A ⟶ B) (b : A' ⟶ B') (l : A ⟶ A') (r : B ⟶ B')
    (lm : X ⟶ X') (rm : Y ⟶ Y')
    (hl : lm ≫ s'.hom=s.hom ≫ F.map l)
    (hr : rm ≫ t'.hom=t.hom ≫ F.map r) (h : a ≫ r=l ≫ b) :
    (s.hom ≫ F.map a ≫ t.inv) ≫ rm=lm ≫ (s'.hom ≫ F.map b ≫ t'.inv) := by
  apply (cancel_mono t'.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [hr]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [← F.map_comp,h,F.map_comp]
  simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map b) hl.symm

/-- The actual sheaf overlap square gives the corresponding module square
using naturality of the original section comparisons at both endpoints. -/
lemma sheaf_square (L K : Line (Spec S)) (h : L.object ⟶ K.object)
    (a : OriginalLineOverlapCoaction318.first R S L ⟶ OriginalLineOverlapCoaction318.second R S L)
    (b : OriginalLineOverlapCoaction318.first R S K ⟶ OriginalLineOverlapCoaction318.second R S K)
    (hab : a ≫ (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map h =
      (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map h ≫ b) :
    OriginalLineOverlapCoaction318.moduleHomEquiv R S L a ≫
      (ModuleCat.extendScalars (rightMap R S S).hom).map (moduleSpecΓFunctor.map h) =
    (ModuleCat.extendScalars (leftMap R S S).hom).map (moduleSpecΓFunctor.map h) ≫
      OriginalLineOverlapCoaction318.moduleHomEquiv R S K b := by
  have ha : OriginalLineOverlapCoaction318.moduleHomEquiv R S L a=
      (sectionsIso (leftMap R S S) L).hom ≫
      (moduleSpecΓFunctor (R := ring R S S)).map
        (X := (Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object)
        (Y := (Scheme.Modules.pullback (Spec.map (rightMap R S S))).obj L.object) a ≫
      (sectionsIso (rightMap R S S) L).inv :=
    OriginalLineOverlapCoaction318.moduleHomEquiv_apply R S L a
  have hb : OriginalLineOverlapCoaction318.moduleHomEquiv R S K b=
      (sectionsIso (leftMap R S S) K).hom ≫
      (moduleSpecΓFunctor (R := ring R S S)).map
        (X := (Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj K.object)
        (Y := (Scheme.Modules.pullback (Spec.map (rightMap R S S))).obj K.object) b ≫
      (sectionsIso (rightMap R S S) K).inv :=
    OriginalLineOverlapCoaction318.moduleHomEquiv_apply R S K b
  have hs := conjugate_square (moduleSpecΓFunctor (R := ring R S S))
    (A := (Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object)
    (B := (Scheme.Modules.pullback (Spec.map (rightMap R S S))).obj L.object)
    (A' := (Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj K.object)
    (B' := (Scheme.Modules.pullback (Spec.map (rightMap R S S))).obj K.object)
    (sectionsIso (leftMap R S S) L) (sectionsIso (rightMap R S S) L)
    (sectionsIso (leftMap R S S) K) (sectionsIso (rightMap R S S) K) a b
    ((Scheme.Modules.pullback (Spec.map (leftMap R S S))).map h)
    ((Scheme.Modules.pullback (Spec.map (rightMap R S S))).map h)
    ((ModuleCat.extendScalars (leftMap R S S).hom).map (moduleSpecΓFunctor.map h))
    ((ModuleCat.extendScalars (rightMap R S S).hom).map (moduleSpecΓFunctor.map h))
    (OriginalLineComparisonComposition318.sectionsIso_naturality (leftMap R S S) L K h)
    (OriginalLineComparisonComposition318.sectionsIso_naturality (rightMap R S S) L K h) hab
  exact (congrArg (fun k => k ≫
    (ModuleCat.extendScalars (rightMap R S S).hom).map (moduleSpecΓFunctor.map h)) ha).trans
    (hs.trans (congrArg (fun k =>
      (ModuleCat.extendScalars (leftMap R S S).hom).map (moduleSpecΓFunctor.map h) ≫ k) hb.symm))

lemma geometric_coaction (L K : Line (Spec S)) (h : L.object ⟶ K.object)
    (a : OriginalLineOverlapCoaction318.first R S L ⟶ OriginalLineOverlapCoaction318.second R S L)
    (b : OriginalLineOverlapCoaction318.first R S K ⟶ OriginalLineOverlapCoaction318.second R S K)
    (hab : a ≫ (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map h =
      (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map h ≫ b) :
    OriginalLineOverlapCoaction318.homEquiv R S L a ≫
      (pullPush R S S).map (moduleSpecΓFunctor.map h) =
    moduleSpecΓFunctor.map h ≫ OriginalLineOverlapCoaction318.homEquiv R S K b :=
  module_coaction R S _ _ _ (sheaf_square R S L K h a b hab)
end OverlapMorphismCoaction318
