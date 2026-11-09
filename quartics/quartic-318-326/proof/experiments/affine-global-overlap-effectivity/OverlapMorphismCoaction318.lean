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
  rw [homEquiv_apply, homEquiv_apply, Category.assoc]
  change _ ≫ ((naturalIso R S S).hom.app N ≫ (pullPush R S S).map h) = _
  rw [← (naturalIso R S S).hom.naturality h, ← Category.assoc,
    ← Adjunction.homEquiv_naturality_right, hab,
    Adjunction.homEquiv_naturality_left, Category.assoc]

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
  apply (cancel_mono (sectionsIso (rightMap R S S) K).hom).mp
  simp only [OriginalLineOverlapCoaction318.moduleHomEquiv_apply, Category.assoc]
  rw [OriginalLineComparisonComposition318.sectionsIso_naturality (rightMap R S S) L K h]
  simp only [Iso.inv_hom_id_assoc]
  rw [OriginalLineComparisonComposition318.sectionsIso_naturality_assoc (leftMap R S S) L K h]
  rw [← Functor.map_comp, ← Functor.map_comp, hab]

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
