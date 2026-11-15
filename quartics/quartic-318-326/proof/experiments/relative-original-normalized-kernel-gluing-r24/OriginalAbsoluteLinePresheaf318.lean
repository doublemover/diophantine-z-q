module
public import ContactUniversalFrameClassifier318
public import RelativeLineClassBaseChange318
public import RelativeFppfLineSheaf318
public section
noncomputable section
namespace OriginalAbsoluteLinePresheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
universe u
variable {X S T T' T'' : Scheme.{u}} (p : X ⟶ S)
abbrev TestClass (t : T ⟶ S) := Class (pullback p t)
@[expose] def map (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T) (ha : a ≫ t=t') :
    TestClass p t →* TestClass p t' :=
  LineClassPullbackHom318.pullback (RelativeLineClassBaseChange318.totalMap p t t' a ha)
lemma identity (t : T ⟶ S) (ha : (𝟙 T) ≫ t=t) : map p t t (𝟙 T) ha=MonoidHom.id _ := by
  rw [map,RelativeLineClassBaseChange318.totalMap_identity,LineClassPullbackHom318.identity]
lemma composition (t : T ⟶ S) (t' : T' ⟶ S) (t'' : T'' ⟶ S)
    (a : T' ⟶ T) (a' : T'' ⟶ T') (ha : a ≫ t=t') (ha' : a' ≫ t'=t'')
    (hc : (a' ≫ a) ≫ t=t'') :
    map p t t'' (a' ≫ a) hc=(map p t' t'' a' ha').comp (map p t t' a ha) := by
  change LineClassPullbackHom318.pullback (RelativeLineClassBaseChange318.totalMap p t t'' (a' ≫ a) hc)=_
  rw [RelativeLineClassBaseChange318.totalMap_composition p t t' t'' a a' ha ha' hc,
    LineClassPullbackHom318.composition]
  rfl
/-- Absolute ORIGINAL line classes on every actual base-changed family.
No quotient or sheafification is inserted in this presheaf. -/
@[expose] def presheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u+1} where
  obj t := CommGrpCat.of (TestClass p t.unop.hom)
  map f := CommGrpCat.ofHom (map p _ _ f.unop.left f.unop.w)
  map_id t := CommGrpCat.hom_ext (identity p t.unop.hom _)
  map_comp f g := CommGrpCat.hom_ext
    (composition p _ _ _ f.unop.left g.unop.left f.unop.w g.unop.w _)
/-- The actual quotient by original base-line pullbacks, on all tests. -/
@[expose] def quotient : presheaf p ⟶ RelativeLineClassBaseChange318.presheaf p where
  app t := CommGrpCat.ofHom (RelativeLineClassQuotient318.classMap (pullback.snd p t.unop.hom))
  naturality _ _ f := by
    apply CommGrpCat.hom_ext
    ext x
    rfl
@[expose] def value : presheaf p ⟶ (RelativeFppfLineSheaf318.sheaf p).obj :=
  quotient p ≫ RelativeFppfLineSheaf318.unit p
lemma on_line (B : Over S) (L : Line (pullback p B.hom)) :
    (value p).app (op B) (classOf L)=
      (RelativeFppfLineSheaf318.unit p).app (op B)
        (RelativeLineClassQuotient318.classMap (pullback.snd p B.hom) (classOf L)) := rfl
end OriginalAbsoluteLinePresheaf318
