module
public import OriginalPulledDifferenceIsomEquivalence318
public import ContactBoundedAbelGeometricRelation318
public section
noncomputable section
namespace ContactWholeIsomPointEquivalence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
variable (T : Scheme.{0}) (b : T ⟶ Spec R)
local notation "m" => pullback.fst p b
local notation "Points" => {z : T ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K //
  z ≫ ContactGeometricIsomRelationWitness318.projection R c L K=b}
/-- Every WHOLE coefficient test now has an actual bijection between
points of the SAME frame parameter and full original pulled line isomorphisms.
This is not yet a natural represented-Isom statement: coefficient naturality
of this specific tensor comparison remains a separate obligation. -/
@[expose] def equivalence : Points ≃
    ((LineSheafPullback318.line m L).object ≅ (LineSheafPullback318.line m K).object) :=
  (ContactWholeSchemeFrameParameter318.equivalence R c D T b).trans
    (OriginalPulledDifferenceIsomEquivalence318.equivalence m L K).symm
/-- The inverse direction is EXACTLY the previously constructed original
pointOfIso, not an arbitrary unrelated set-theoretic bijection. -/
lemma inverse_is_original
    (e : (LineSheafPullback318.line m L).object ≅ (LineSheafPullback318.line m K).object) :
    (equivalence R c L K T b).symm e=
      ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b e := rfl
lemma classify_recover (z : Points) :
    ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b
      (equivalence R c L K T b z)=z :=
  (equivalence R c L K T b).symm_apply_apply z
lemma recover_classify
    (e : (LineSheafPullback318.line m L).object ≅ (LineSheafPullback318.line m K).object) :
    equivalence R c L K T b (ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b e)=e :=
  (equivalence R c L K T b).apply_symm_apply e
lemma unique_point
    (e : (LineSheafPullback318.line m L).object ≅ (LineSheafPullback318.line m K).object) :
    ∃! z : Points, equivalence R c L K T b z=e := by
  refine ⟨(equivalence R c L K T b).symm e,(equivalence R c L K T b).apply_symm_apply e,?_⟩
  intro z hz
  apply (equivalence R c L K T b).injective
  exact hz.trans ((equivalence R c L K T b).apply_symm_apply e).symm
end ContactWholeIsomPointEquivalence318
