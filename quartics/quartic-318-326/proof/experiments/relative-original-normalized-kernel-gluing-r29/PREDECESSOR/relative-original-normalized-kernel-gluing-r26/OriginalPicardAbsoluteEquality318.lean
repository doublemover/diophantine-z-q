module
public import OriginalRelativeLocalAbsoluteEquality318
public import OriginalFppfClassEquality318
public section
noncomputable section
namespace OriginalPicardAbsoluteEquality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
variable {X S : Scheme.{0}} (p : X ⟶ S)
local notation "P" => OriginalAbsoluteLinePresheaf318.presheaf p
local notation "Q" => OriginalAbsoluteLinePresheaf318.quotient p
local notation "V" => OriginalAbsoluteLinePresheaf318.value p
local notation "J" => RelativeFppfLineSheaf318.topology S
lemma pullback_equalizer (B T : Over S) (f : T ⟶ B) (x y : P.obj (op B)) :
    (Presheaf.equalizerSieve x y).pullback f=
      Presheaf.equalizerSieve (P.map f.op x) (P.map f.op y) := by
  ext U g
  change P.map (f.op ≫ g.op) x=P.map (f.op ≫ g.op) y ↔
    P.map g.op (P.map f.op x)=P.map g.op (P.map f.op y)
  rw [P.map_comp]
  rfl
/-- The actual original fppf Picard equality is precisely local ABSOLUTE
line-isomorphism equality. The base-twist is removed on its genuine
trivializing cover, never by assuming the naive quotient unit injective. -/
lemma iff_covering (B : Over S) (x y : P.obj (op B)) :
    V.app (op B) x=V.app (op B) y ↔ Presheaf.equalizerSieve x y ∈ J B := by
  constructor
  · intro h
    have hr : Presheaf.equalizerSieve (Q.app (op B) x) (Q.app (op B) y) ∈ J B :=
      (OriginalFppfClassEquality318.iff_covering p B _ _).mp h
    apply J.transitive hr (Presheaf.equalizerSieve x y)
    intro T f hf
    rw [pullback_equalizer]
    apply OriginalRelativeLocalAbsoluteEquality318.covering p T
    have hx := ConcreteCategory.congr_hom (Q.naturality f.op) x
    have hy := ConcreteCategory.congr_hom (Q.naturality f.op) y
    change (RelativeLineClassBaseChange318.presheaf p).map f.op (Q.app (op B) x)=
      (RelativeLineClassBaseChange318.presheaf p).map f.op (Q.app (op B) y) at hf
    exact hx.trans (hf.trans hy.symm)
  · intro h
    have hf : Presheaf.IsSheaf J ((RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1}) :=
      (Presheaf.isSheaf_iff_isSheaf_forget (forget CommGrpCat.{1})).mp
        (RelativeFppfLineSheaf318.sheaf p).property
    have ht := (isSheaf_iff_isSheaf_of_type _ _).mp hf
    apply (ht.isSeparated _ h).ext
    intro T f he
    have hx := ConcreteCategory.congr_hom (V.naturality f.op) x
    have hy := ConcreteCategory.congr_hom (V.naturality f.op) y
    change P.map f.op x=P.map f.op y at he
    exact hx.symm.trans ((congrArg (V.app (op T)) he).trans hy)
/-- Membership keeps the full original module objects on the actual
canonical changed family, for every arrow in the original big site. -/
lemma line_membership (B T : Over S) (f : T ⟶ B)
    (L K : Line (pullback p B.hom)) :
    Presheaf.equalizerSieve (show P.obj (op B) from classOf L)
      (show P.obj (op B) from classOf K) f ↔
    Nonempty ((LineSheafPullback318.line
      (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w) L).object ≅
      (LineSheafPullback318.line
        (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w) K).object) :=
  classOf_eq_iff _ _
end OriginalPicardAbsoluteEquality318
