module
public import ContactBoundedRankData318
public section
noncomputable section
namespace ContactBoundedClassifyingMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedSchemeHilbertData318.Data c N b)
local notation "U" => ContactBoundedRankCover318.cover c N b D
local notation "m" => ContactBoundedRankData318.map c N b D
lemma compatible (d e : Fin (N+1)) : pullback.fst (U.f d) (U.f e) ≫ m d=
    pullback.snd (U.f d) (U.f e) ≫ m e := by
  by_cases h : d=e
  · subst e
    have hh : pullback.fst (U.f d) (U.f d)=pullback.snd (U.f d) (U.f d) :=
      (cancel_mono (U.f d)).mp pullback.condition
    rw [hh]
  · letI := ContactBoundedRankCover318.intersection_empty c N b D d e h
    exact Scheme.isInitialOfIsEmpty.hom_ext _ _
/-- Genuine bounded-varying-rank classifying map on an arbitrary
coefficient scheme, assembled from the derived clopen rank cover. -/
@[expose] def classify : B ⟶ ContactBoundedHilbertParameter318.scheme c N :=
  U.glueMorphisms m (compatible c N b D)
@[reassoc] lemma evaluate (d : Fin (N+1)) : U.f d ≫ classify c N b D=m d :=
  U.ι_glueMorphisms m (compatible c N b D) d
lemma over : classify c N b D ≫ ContactBoundedHilbertParameter318.structureMap c N=b := by
  apply U.hom_ext
  intro d
  rw [← Category.assoc,evaluate]
  exact ContactBoundedRankData318.over c N b D d
end ContactBoundedClassifyingMap318
