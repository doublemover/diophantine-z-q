module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace NativeOverlapPullbackComparison318
open AlgebraicGeometry CategoryTheory
universe u
variable {A B C D X : Scheme.{u}} (j : D ⟶ C) (i : C ⟶ A) (k : D ⟶ B)
  (f : A ⟶ X) (g : B ⟶ X) (h : j ≫ i ≫ f=k ≫ g)

/-- All four constituents are the native composition/congruence isomorphisms.
In particular h is a proved equality of maps, not an identification by type. -/
@[expose] def functorIso :
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i) ⋙ Scheme.Modules.pullback j ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback k :=
  Functor.isoWhiskerRight (Scheme.Modules.pullbackComp i f) (Scheme.Modules.pullback j) ≪≫
  Scheme.Modules.pullbackComp j (i ≫ f) ≪≫
  Scheme.Modules.pullbackCongr h ≪≫ (Scheme.Modules.pullbackComp k g).symm

@[expose] def iso (F : X.Modules) :
    (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj F)) ≅
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj F) :=
  (functorIso j i k f g h).app F

lemma forward_backward (F : X.Modules) :
    (iso j i k f g h F).hom ≫ (iso j i k f g h F).inv=𝟙 _ :=
  (iso j i k f g h F).hom_inv_id

lemma naturality {F G : X.Modules} (u : F ⟶ G) :
    (Scheme.Modules.pullback j).map
      ((Scheme.Modules.pullback i).map ((Scheme.Modules.pullback f).map u)) ≫
        (iso j i k f g h G).hom=
    (iso j i k f g h F).hom ≫
      (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map u) :=
  (functorIso j i k f g h).hom.naturality u
end NativeOverlapPullbackComparison318
