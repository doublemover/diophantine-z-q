module
public import RelativeLineClassBaseChange318
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public section
noncomputable section
namespace RelativeLineBaseChangeIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
universe u
variable {X Y S S' T T' : Scheme.{u}}

/-- The original relative quotient respects an actual scheme isomorphism
over the unchanged base, via its original pullback and inverse pullback. -/
@[expose] def relativeIso (p : X ⟶ S) (q : Y ⟶ S) (e : Y ≅ X)
    (overBase : e.hom ≫ p = q) :
    CommGrpCat.of (RelativeClass p) ≅ CommGrpCat.of (RelativeClass q) where
  hom := CommGrpCat.ofHom (RelativeLineClassQuotient318.map p q e.hom (𝟙 S)
    (by simpa using overBase))
  inv := CommGrpCat.ofHom (RelativeLineClassQuotient318.map q p e.inv (𝟙 S)
    (by rw [← overBase, ← Category.assoc, e.inv_hom_id]; simp))
  hom_inv_id := by
    apply CommGrpCat.hom_ext
    ext c
    obtain ⟨d, rfl⟩ := classMap_surjective p c
    change classMap p
        (LineClassPullbackHom318.pullback e.inv (LineClassPullbackHom318.pullback e.hom d)) =
      classMap p d
    simp only [LineClassPullbackHom318.apply_eq,
      ← LineClassPullbackLaws318.pullback_composition, e.inv_hom_id,
      LineClassPullbackLaws318.pullback_identity]
  inv_hom_id := by
    apply CommGrpCat.hom_ext
    ext c
    obtain ⟨d, rfl⟩ := classMap_surjective q c
    change classMap q
        (LineClassPullbackHom318.pullback e.hom (LineClassPullbackHom318.pullback e.inv d)) =
      classMap q d
    simp only [LineClassPullbackHom318.apply_eq,
      ← LineClassPullbackLaws318.pullback_composition, e.hom_inv_id,
      LineClassPullbackLaws318.pullback_identity]

/-- The actual iterated full fiber product is identified with the actual
fiber product for the composite base map. -/
@[expose] def fiberIso (p : X ⟶ S) (b : S' ⟶ S) (t : T ⟶ S') :
    pullback (pullback.snd p b) t ≅ pullback p (t ≫ b) :=
  pullbackLeftPullbackSndIso p b t

@[reassoc] lemma fiberIso_fst (p : X ⟶ S) (b : S' ⟶ S) (t : T ⟶ S') :
    (fiberIso p b t).hom ≫ pullback.fst p (t ≫ b) =
      pullback.fst (pullback.snd p b) t ≫ pullback.fst p b :=
  pullbackLeftPullbackSndIso_hom_fst p b t

@[reassoc] lemma fiberIso_snd (p : X ⟶ S) (b : S' ⟶ S) (t : T ⟶ S') :
    (fiberIso p b t).hom ≫ pullback.snd p (t ≫ b) =
      pullback.snd (pullback.snd p b) t :=
  pullbackLeftPullbackSndIso_hom_snd p b t

lemma fiberIso_naturality (p : X ⟶ S) (b : S' ⟶ S)
    (t : T ⟶ S') (t' : T' ⟶ S') (a : T' ⟶ T) (ha : a ≫ t = t')
    (hc : a ≫ (t ≫ b) = t' ≫ b) :
    (fiberIso p b t').hom ≫ totalMap p (t ≫ b) (t' ≫ b) a hc =
      totalMap (pullback.snd p b) t t' a ha ≫ (fiberIso p b t).hom := by
  apply pullback.hom_ext <;>
    simp [fiberIso, totalMap, Category.assoc]

/-- Pointwise original-relative-class comparison, using the actual fiber
product isomorphism and the exact original quotient maps. -/
@[expose] def componentIso (p : X ⟶ S) (b : S' ⟶ S) (t : T ⟶ S') :
    CommGrpCat.of (TestClass p (t ≫ b)) ≅
      CommGrpCat.of (TestClass (pullback.snd p b) t) :=
  relativeIso (pullback.snd p (t ≫ b)) (pullback.snd (pullback.snd p b) t)
    (fiberIso p b t) (fiberIso_snd p b t)

/-- Restricting the original relative presheaf to the new base gives the
original relative presheaf of the actual base-changed family, naturally. -/
@[expose] def presheafIso (p : X ⟶ S) (b : S' ⟶ S) :
    (Over.map b).op ⋙ presheaf p ≅ presheaf (pullback.snd p b) :=
  NatIso.ofComponents (fun T => componentIso p b T.unop.hom) (by
    intro T V g
    apply CommGrpCat.hom_ext
    ext c
    obtain ⟨d, rfl⟩ := classMap_surjective (pullback.snd p (T.unop.hom ≫ b)) c
    change classMap (pullback.snd (pullback.snd p b) V.unop.hom)
        (LineClassPullbackHom318.pullback (fiberIso p b V.unop.hom).hom
          (LineClassPullbackHom318.pullback
            (totalMap p (T.unop.hom ≫ b) (V.unop.hom ≫ b) g.unop.left _) d)) =
      classMap (pullback.snd (pullback.snd p b) V.unop.hom)
        (LineClassPullbackHom318.pullback
          (totalMap (pullback.snd p b) T.unop.hom V.unop.hom g.unop.left g.unop.w)
          (LineClassPullbackHom318.pullback (fiberIso p b T.unop.hom).hom d))
    simp only [LineClassPullbackHom318.apply_eq]
    rw [← LineClassPullbackLaws318.pullback_composition, fiberIso_naturality,
      LineClassPullbackLaws318.pullback_composition])
end RelativeLineBaseChangeIso318
