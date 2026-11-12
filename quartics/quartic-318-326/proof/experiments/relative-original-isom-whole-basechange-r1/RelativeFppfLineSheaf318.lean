module
public import RelativeLineFunctorPullback318
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public section
noncomputable section
namespace RelativeFppfLineSheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y S : Scheme.{u}}

/-- The actual big fppf topology on schemes over the original base. -/
@[expose] def topology (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

instance topology_subcanonical (S : Scheme.{u}) : (topology S).Subcanonical :=
  inferInstanceAs (Scheme.fppfTopology.over S).Subcanonical

/-- Construct the required filtered colimits from the explicit commutative-group
colimit cocones. No sheafification-existence premise is supplied by a caller. -/
instance coverColimits (S : Scheme.{u}) (T : Over S) :
    HasColimitsOfShape ((topology S).Cover T)ᵒᵖ CommGrpCat.{u+1} where
  has_colimit F := HasColimit.mk ⟨CommGrpCat.FilteredColimits.colimitCocone.{u+1,0} F,
    CommGrpCat.FilteredColimits.colimitCoconeIsColimit.{u+1,0} F⟩

/-- The original universe of line classes accommodates all covers of the big
site. Concrete limits and filtered colimits give actual left-exact sheafification. -/
instance hasSheafification (S : Scheme.{u}) : HasSheafify (topology S) CommGrpCat.{u+1} :=
  inferInstance

/-- The associated fppf group sheaf of the actual naive relative Picard presheaf.
This does not assert representability or identify a degree-zero component. -/
@[expose] def sheaf (p : X ⟶ S) : Sheaf (topology S) CommGrpCat.{u+1} :=
  (presheafToSheaf (topology S) CommGrpCat.{u+1}).obj
    (RelativeLineClassBaseChange318.presheaf p)

lemma isSheaf (p : X ⟶ S) : Presheaf.IsSheaf (topology S) (sheaf p).obj :=
  (sheaf p).property

/-- The actual universal map from original relative classes to their fppf sheaf. -/
@[expose] def unit (p : X ⟶ S) :
    RelativeLineClassBaseChange318.presheaf p ⟶ (sheaf p).obj :=
  toSheafify (topology S) (RelativeLineClassBaseChange318.presheaf p)

/-- Maps into any fppf group sheaf factor through this specific associated sheaf. -/
@[expose] def lift (p : X ⟶ S) (F : Sheaf (topology S) CommGrpCat.{u+1})
    (a : RelativeLineClassBaseChange318.presheaf p ⟶ F.obj) : sheaf p ⟶ F :=
  ⟨sheafifyLift (topology S) a F.property⟩

lemma unit_lift (p : X ⟶ S) (F : Sheaf (topology S) CommGrpCat.{u+1})
    (a : RelativeLineClassBaseChange318.presheaf p ⟶ F.obj) :
    unit p ≫ (lift p F a).hom = a :=
  toSheafify_sheafifyLift (topology S) a F.property

lemma lift_unique (p : X ⟶ S) (F : Sheaf (topology S) CommGrpCat.{u+1})
    (a : RelativeLineClassBaseChange318.presheaf p ⟶ F.obj) (g : sheaf p ⟶ F)
    (h : unit p ≫ g.hom = a) : g = lift p F a := by
  apply Sheaf.hom_ext
  exact sheafifyLift_unique (topology S) a F.property g.hom h

variable (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (overBase : f ≫ q = p)

/-- The actual pullback transformation extends to the actual associated sheaves. -/
@[expose] def pullback : sheaf q ⟶ sheaf p :=
  (presheafToSheaf (topology S) CommGrpCat.{u+1}).map
    (RelativeLineFunctorPullback318.transformation p q f overBase)

lemma unit_pullback :
    RelativeLineFunctorPullback318.transformation p q f overBase ≫ unit p =
      unit q ≫ (pullback p q f overBase).hom :=
  toSheafify_naturality (topology S)
    (RelativeLineFunctorPullback318.transformation p q f overBase)

/-- The sheaf morphism is uniquely determined by the unchanged original
pullback and both canonical unit maps. -/
lemma pullback_unique (g : sheaf q ⟶ sheaf p)
    (h : unit q ≫ g.hom =
      RelativeLineFunctorPullback318.transformation p q f overBase ≫ unit p) :
    g = pullback p q f overBase := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (topology S) _ _ (sheaf p).property
  exact h.trans (unit_pullback p q f overBase)
end RelativeFppfLineSheaf318
