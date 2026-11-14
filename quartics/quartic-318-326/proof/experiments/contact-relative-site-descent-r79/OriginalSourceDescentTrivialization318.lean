module
public import ActualDescentEvaluationChange318
public section
noncomputable section
namespace OriginalSourceDescentTrivialization318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualOverlapDiagram318
open OriginalSchemeDescentData318 ActualDescentTestEvaluation318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y T : Scheme.{u}} {f : X ⟶ Y} (D : Datum f)

lemma equal_pair (x y : T ⟶ X) (he : x = y) (h : x ≫ f = y ≫ f) :
    map D x y h = (Scheme.Modules.pullbackCongr he).hom.app D.line.object := by
  subst y
  simpa only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app] using self D x

lemma path_equal {V : Scheme.{u}} (M : X.Modules) (a : V ⟶ X)
    (p q : T ⟶ V) (x y : T ⟶ X) (hp : p ≫ a = x) (hq : q ≫ a = y) (he : x = y) :
    (PullbackPathComposition318.iso p a x hp).hom.app M ≫
      (Scheme.Modules.pullbackCongr he).hom.app M ≫
        (PullbackPathComposition318.iso q a y hq).inv.app M =
    CanonicalSheafOverlap318.overlap M a p q x hp (hq.trans he.symm) := by
  subst y
  simp only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app,
    Category.id_comp,CanonicalSheafOverlap318.overlap]

variable (g : T ⟶ X)
/-- Pulling original descent data back to its own covering scheme gives
the canonical descent data of its original line. The overlap equality is
derived from its diagonal, with both original endpoint paths retained. -/
lemma overlap : (OriginalSchemeDescentBaseChange318.datum f g g f rfl D).overlap =
    (OriginalCanonicalDescent318.datum g D.line).overlap := by
  rw [ActualDescentEvaluationChange318.overlap,
    equal_pair D (first g ≫ g) (second g ≫ g) (edge_condition g)]
  exact path_equal D.line.object g (first g) (second g)
    (first g ≫ g) (second g ≫ g) rfl rfl (edge_condition g)

@[expose] def hom : OriginalSchemeDescentBaseChangeMaps318.Hom
    (OriginalSchemeDescentBaseChange318.datum f g g f rfl D)
    (OriginalCanonicalDescent318.datum g D.line) where
  sheafHom := 𝟙 _
  commutes := by
    simp only [Functor.map_id,Category.comp_id,Category.id_comp]
    exact overlap D g
end OriginalSourceDescentTrivialization318
