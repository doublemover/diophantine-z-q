module
public import RelativeLineClassBaseChange318
public section
noncomputable section
namespace RelativeLineFunctorPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
universe u
variable {X Y S T T' : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (f : X ⟶ Y) (overBase : f ≫ q = p)

/-- The base change of the original scheme morphism, retaining both original
fiber-product projections and the exact structure square. -/
@[expose] def baseMap (t : T ⟶ S) : pullback p t ⟶ pullback q t :=
  pullback.lift (pullback.fst p t ≫ f) (pullback.snd p t) (by
    rw [Category.assoc, overBase]
    exact pullback.condition)

lemma baseMap_fst (t : T ⟶ S) :
    baseMap p q f overBase t ≫ pullback.fst q t = pullback.fst p t ≫ f :=
  pullback.lift_fst _ _ _

lemma baseMap_snd (t : T ⟶ S) :
    baseMap p q f overBase t ≫ pullback.snd q t = pullback.snd p t :=
  pullback.lift_snd _ _ _

lemma baseMap_naturality (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') :
    totalMap p t t' a ha ≫ baseMap p q f overBase t =
      baseMap p q f overBase t' ≫ totalMap q t t' a ha := by
  apply pullback.hom_ext <;> simp [baseMap, totalMap, Category.assoc]

/-- Pullback along the actual base-changed original map descends through the
actual subgroup of test-base lines. -/
@[expose] def relativeMap (t : T ⟶ S) : TestClass q t →* TestClass p t :=
  RelativeLineClassQuotient318.map (pullback.snd q t) (pullback.snd p t)
    (baseMap p q f overBase t) (𝟙 T) (by
      rw [Category.comp_id]
      exact baseMap_snd p q f overBase t)

lemma relativeMap_class (t : T ⟶ S) (c : LineSheafClass318.Class (pullback q t)) :
    relativeMap p q f overBase t (classMap (pullback.snd q t) c) =
      classMap (pullback.snd p t)
        (LineClassPullbackHom318.pullback (baseMap p q f overBase t) c) := rfl

lemma relativeMap_naturality (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T)
    (ha : a ≫ t = t') :
    (relativeMap p q f overBase t').comp (testMap q t t' a ha) =
      (testMap p t t' a ha).comp (relativeMap p q f overBase t) := by
  ext c
  obtain ⟨d, rfl⟩ := classMap_surjective (pullback.snd q t) c
  change classMap (pullback.snd p t')
      (LineClassPullbackHom318.pullback (baseMap p q f overBase t')
        (LineClassPullbackHom318.pullback (totalMap q t t' a ha) d)) =
    classMap (pullback.snd p t')
      (LineClassPullbackHom318.pullback (totalMap p t t' a ha)
        (LineClassPullbackHom318.pullback (baseMap p q f overBase t) d))
  simp only [LineClassPullbackHom318.apply_eq]
  rw [← LineClassPullbackLaws318.pullback_composition,
    ← LineClassPullbackLaws318.pullback_composition,
    baseMap_naturality p q f overBase t t' a ha]

/-- The pullback natural transformation on the actual naive relative Picard
presheaves. No represented-group map or norm transformation is asserted. -/
@[expose] def transformation : presheaf q ⟶ presheaf p where
  app t := CommGrpCat.ofHom (relativeMap p q f overBase t.unop.hom)
  naturality _ _ h := CommGrpCat.hom_ext
    (relativeMap_naturality p q f overBase _ _ h.unop.left h.unop.w)
end RelativeLineFunctorPullback318
