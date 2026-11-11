module
public import AffineClosedIdealBaseChange318
public section
noncomputable section
namespace AffineClosedRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
variable (A : CommRingCat.{u}) (j : Spec A ⟶ X)
abbrev scheme := pullback p j
abbrev into := pullback.snd p j
abbrev ideal : Ideal A := AffineClosedQuotientExtraction318.ideal A (into p A j)
abbrev comparison : scheme p A j ≅ Spec (CommRingCat.of (A ⧸ ideal p A j)) :=
  AffineClosedQuotientExtraction318.comparison A (into p A j)
variable (B : CommRingCat.{u}) (φ : A ⟶ B)
local notation "k" => Spec.map φ
@[expose] def map : scheme p B (k ≫ j) ⟶ scheme p A j :=
  pullback.lift (pullback.fst p (k ≫ j)) (pullback.snd p (k ≫ j) ≫ k)
    (by rw [Category.assoc]; exact pullback.condition)
@[reassoc] lemma map_fst : map p A j B φ ≫ pullback.fst p j=pullback.fst p (k ≫ j) :=
  pullback.lift_fst _ _ _
@[reassoc] lemma map_into : map p A j B φ ≫ into p A j=into p B (k ≫ j) ≫ k :=
  pullback.lift_snd _ _ _
lemma cartesian : IsPullback (map p A j B φ) (into p B (k ≫ j)) (into p A j) k := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p j) (h₂₂ := j)
  · simpa only [map_fst] using (IsPullback.of_hasPullback p (k ≫ j))
  · exact map_into p A j B φ
  · exact IsPullback.of_hasPullback p j
/-- Full affine restriction ideals commute with arbitrary further affine
restriction, proved through the actual Cartesian closed models. -/
lemma ideal_map : ideal p B (k ≫ j)=Ideal.map φ.hom (ideal p A j) :=
  AffineClosedIdealBaseChange318.ideal_map A B φ.hom (into p A j)
    (into p B (k ≫ j)) (map p A j B φ) (cartesian p A j B φ)
end AffineClosedRestriction318
