module
public import RelativeFamilyFrameRule318
public section
noncomputable section
namespace RelativeFamilyFrameGraph318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
  (F : RelativeFamilyFrameRule318.Rule p L)
@[expose] def graph (S : CommRingCat.{u}) (x : Spec S ⟶ X) : Spec S ⟶ pullback p (x ≫ p) :=
  pullback.lift x (𝟙 _) (by simp only [Category.id_comp])
@[reassoc] lemma graph_fst (S : CommRingCat.{u}) (x : Spec S ⟶ X) :
    graph p S x ≫ pullback.fst p (x ≫ p)=x := pullback.lift_fst _ _ _
@[reassoc] lemma graph_snd (S : CommRingCat.{u}) (x : Spec S ⟶ X) :
    graph p S x ≫ pullback.snd p (x ≫ p)=𝟙 _ := pullback.lift_snd _ _ _
@[expose] def frame (S : CommRingCat.{u}) (x : Spec S ⟶ X) : Frames (LineSheafPullback318.line x L) :=
  OriginalFramePathTransport318.transport L (graph p S x) (pullback.fst p (x ≫ p)) x
    (graph_fst p S x) (F.app S (x ≫ p))
lemma square (S T : CommRingCat.{u}) (g : Spec T ⟶ Spec S)
    (x : Spec S ⟶ X) (y : Spec T ⟶ X) (h : g ≫ x=y) :
    g ≫ graph p S x=graph p T y ≫
      RelativeSchemeCoefficient318.map p (x ≫ p) (y ≫ p) g
        (by rw [←Category.assoc,h]) := by
  apply pullback.hom_ext
  · rw [Category.assoc,graph_fst,Category.assoc,RelativeSchemeCoefficient318.map_fst,graph_fst,h]
  · rw [Category.assoc,graph_snd,Category.comp_id,Category.assoc,
      RelativeSchemeCoefficient318.map_snd,←Category.assoc,graph_snd,Category.id_comp]
end RelativeFamilyFrameGraph318
