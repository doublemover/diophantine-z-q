module
public import RelativeLineClassQuotient318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public section
noncomputable section
namespace RelativeLineClassBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassQuotient318
universe u
variable {X S T T' T'' : Scheme.{u}} (p : X ⟶ S)

/-- The naive relative group evaluated on the actual scheme-theoretic fiber
product, not on field-valued points or a chosen model for the fiber. -/
@[expose] def TestClass (t : T ⟶ S) := RelativeClass (pullback.snd p t)

instance testCommGroup (t : T ⟶ S) : CommGroup (TestClass p t) :=
  inferInstanceAs (CommGroup (RelativeClass (pullback.snd p t)))

/-- The actual induced map of fiber products for a morphism of base tests. -/
@[expose] def totalMap (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') : pullback p t' ⟶ pullback p t :=
  pullback.lift (pullback.fst p t') (pullback.snd p t' ≫ a) (by
    rw [Category.assoc, ha]
    exact pullback.condition)

lemma totalMap_fst (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') : totalMap p t t' a ha ≫ pullback.fst p t = pullback.fst p t' :=
  pullback.lift_fst _ _ _

lemma totalMap_snd (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') :
    totalMap p t t' a ha ≫ pullback.snd p t = pullback.snd p t' ≫ a :=
  pullback.lift_snd _ _ _

lemma totalMap_identity (t : T ⟶ S) (ha : (𝟙 T) ≫ t = t) :
    totalMap p t t (𝟙 T) ha = 𝟙 (pullback p t) := by
  apply pullback.hom_ext <;> simp [totalMap]

lemma totalMap_composition (t : T ⟶ S) (t' : T' ⟶ S) (t'' : T'' ⟶ S)
    (a : T' ⟶ T) (a' : T'' ⟶ T') (ha : a ≫ t = t') (ha' : a' ≫ t' = t'')
    (hc : (a' ≫ a) ≫ t = t'') :
    totalMap p t t'' (a' ≫ a) hc = totalMap p t' t'' a' ha' ≫ totalMap p t t' a ha := by
  apply pullback.hom_ext <;> simp [totalMap, Category.assoc]

/-- Pullback modulo the actual base-line subgroup on arbitrary scheme tests. -/
@[expose] def testMap (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') : TestClass p t →* TestClass p t' :=
  RelativeLineClassQuotient318.map (pullback.snd p t) (pullback.snd p t')
    (totalMap p t t' a ha) a (totalMap_snd p t t' a ha)

lemma testMap_class (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') (c : LineSheafClass318.Class (pullback p t)) :
    testMap p t t' a ha (classMap (pullback.snd p t) c) =
      classMap (pullback.snd p t')
        (LineClassPullbackHom318.pullback (totalMap p t t' a ha) c) := rfl

lemma testMap_identity (t : T ⟶ S) (ha : (𝟙 T) ≫ t = t) :
    testMap p t t (𝟙 T) ha = MonoidHom.id (TestClass p t) := by
  ext c
  obtain ⟨d, rfl⟩ := classMap_surjective (pullback.snd p t) c
  change classMap (pullback.snd p t)
      (LineClassPullbackHom318.pullback (totalMap p t t (𝟙 T) ha) d) =
    classMap (pullback.snd p t) d
  rw [totalMap_identity, LineClassPullbackHom318.identity]
  rfl

lemma testMap_composition (t : T ⟶ S) (t' : T' ⟶ S) (t'' : T'' ⟶ S)
    (a : T' ⟶ T) (a' : T'' ⟶ T') (ha : a ≫ t = t') (ha' : a' ≫ t' = t'')
    (hc : (a' ≫ a) ≫ t = t'') :
    testMap p t t'' (a' ≫ a) hc = (testMap p t' t'' a' ha').comp (testMap p t t' a ha) := by
  ext c
  obtain ⟨d, rfl⟩ := classMap_surjective (pullback.snd p t) c
  change classMap (pullback.snd p t'')
      (LineClassPullbackHom318.pullback (totalMap p t t'' (a' ≫ a) hc) d) =
    classMap (pullback.snd p t'')
      (LineClassPullbackHom318.pullback (totalMap p t' t'' a' ha')
        (LineClassPullbackHom318.pullback (totalMap p t t' a ha) d))
  rw [totalMap_composition p t t' t'' a a' ha ha' hc,
    LineClassPullbackHom318.composition]
  rfl

/-- The actual naive relative Picard presheaf of groups. Sheafification,
representability and its degree-zero/Jacobian component are separate. -/
@[expose] def presheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj t := CommGrpCat.of (TestClass p t.unop.hom)
  map h := CommGrpCat.ofHom (testMap p _ _ h.unop.left h.unop.w)
  map_id t := CommGrpCat.hom_ext (testMap_identity p t.unop.hom _)
  map_comp h k := CommGrpCat.hom_ext
    (testMap_composition p _ _ _ h.unop.left k.unop.left h.unop.w k.unop.w _)
end RelativeLineClassBaseChange318
