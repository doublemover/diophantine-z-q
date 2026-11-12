module
public import ContactProjectiveUniversalRank318
public section
noncomputable section
namespace ClosedFamilyCanonicalProperties318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Y X B : Scheme.{u}} (q : Y ⟶ X) [IsClosedImmersion q] (p : X ⟶ B)
  [IsFinite (q ≫ p)] [Flat (q ≫ p)] [LocallyOfFinitePresentation (q ≫ p)]
abbrev comparison : Y ≅ q.ker.subscheme := asIso q.toImage
@[reassoc] lemma comparison_source : (comparison q).hom ≫ q.ker.subschemeι=q := q.toImage_imageι
lemma projection_eq : q.ker.subschemeι ≫ p=(comparison q).inv ≫ (q ≫ p) := by
  have h := congrArg (fun k => (comparison q).inv ≫ k ≫ p) (comparison_source q)
  simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
instance finite : IsFinite (q.ker.subschemeι ≫ p) := by rw [projection_eq]; infer_instance
instance flat : Flat (q.ker.subschemeι ≫ p) := by rw [projection_eq]; infer_instance
instance presentation : LocallyOfFinitePresentation (q.ker.subschemeι ≫ p) := by rw [projection_eq]; infer_instance
lemma rank (z : B) : (q.ker.subschemeι ≫ p).finrank z=(q ≫ p).finrank z := by
  have H : IsPullback (comparison q).hom (q ≫ p) (q.ker.subschemeι ≫ p) (𝟙 B) :=
    (IsPullback.of_vert_isIso (show CommSq (q ≫ p) (comparison q).hom (𝟙 B) (q.ker.subschemeι ≫ p) from
      ⟨by rw [Category.comp_id,← Category.assoc,comparison_source]⟩)).flip
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ H z).symm
end ClosedFamilyCanonicalProperties318
