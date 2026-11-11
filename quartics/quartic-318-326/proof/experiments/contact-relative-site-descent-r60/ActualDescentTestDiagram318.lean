module
public import OriginalGlobalBaseChangeFunctor318
public section
noncomputable section
namespace ActualDescentTestDiagram318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ActualOverlapDiagram318
universe u
variable {X Y T : Scheme.{u}} (f : X ⟶ Y)

/-- The actual test-point pair in the original categorical double. -/
@[expose] def pair (x y : T ⟶ X) (h : x ≫ f = y ≫ f) : T ⟶ Double f :=
  pullback.lift x y h
@[reassoc] lemma pair_first (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    pair f x y h ≫ first f = x := pullback.lift_fst _ _ _
@[reassoc] lemma pair_second (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    pair f x y h ≫ second f = y := pullback.lift_snd _ _ _

lemma diagonal_pair (x : T ⟶ X) : x ≫ diagonal f = pair f x x rfl := by
  apply pullback.hom_ext
  · simp only [Category.assoc,diagonal_first,Category.comp_id,pair_first]
  · simp only [Category.assoc,diagonal_second,Category.comp_id,pair_second]

/-- A genuine triple in the original adjacent-pair fiber product. -/
@[expose] def triple (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    T ⟶ Triple f :=
  pullback.lift (pair f x y h) (pair f y z k) (by rw [pair_second,pair_first])
@[reassoc] lemma triple_pair01 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ pair01 f = pair f x y h := pullback.lift_fst _ _ _
@[reassoc] lemma triple_pair12 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ pair12 f = pair f y z k := pullback.lift_snd _ _ _
@[reassoc] lemma triple_vertex0 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ vertex0 f = x := by
  rw [vertex0,← Category.assoc,triple_pair01,pair_first]
@[reassoc] lemma triple_vertex1 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ vertex1 f = y := by
  rw [vertex1,← Category.assoc,triple_pair01,pair_second]
@[reassoc] lemma triple_vertex2 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ vertex2 f = z := by
  rw [vertex2,← Category.assoc,triple_pair12,pair_second]
@[reassoc] lemma triple_pair02 (x y z : T ⟶ X) (h : x ≫ f = y ≫ f) (k : y ≫ f = z ≫ f) :
    triple f x y z h k ≫ pair02 f = pair f x z (h.trans k) := by
  apply pullback.hom_ext
  · rw [Category.assoc,pair02_first,triple_vertex0,pair_first]
  · rw [Category.assoc,pair02_second,triple_vertex2,pair_second]
end ActualDescentTestDiagram318
