module
public import WholeMorphismOrbitDescent318
public section
noncomputable section
namespace ContactOriginalIsomOrbitRelation318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomPointOperations318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c))
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "P" => ContactRelationProjectionImage318.object R c L K
local notation "π" => ContactRelationProjectionImage318.projection R c L K
/-- A relation witnessed by actual whole original isomorphisms and
an actual full stabilizer point. No base-Gm replacement is made. -/
def Related (T : Over Q) (z w : T ⟶ P) : Prop :=
  ∃ (b : T.left ⟶ Spec R) (s t : Points R c L K b),
    s.val=z.left ∧ t.val=w.left ∧
      ∃ a : Points R c L L b,composition R c L L K b a t=s
lemma iff_projection (T : Over Q) (z w : T ⟶ P) :
    Related R c L K T z w ↔ z ≫ π=w ≫ π := by
  constructor
  · rintro ⟨b,s,t,hs,ht,a,ha⟩
    apply Over.OverMorphism.ext
    change z.left ≫ ContactGeometricIsomRelationWitness318.projection R c L K=
      w.left ≫ ContactGeometricIsomRelationWitness318.projection R c L K
    rw [←hs,←ht,s.property,t.property]
  · intro h
    let b := w.left ≫ ContactGeometricIsomRelationWitness318.projection R c L K
    let s : Points R c L K b := ⟨z.left,congrArg (fun k => k.left) h⟩
    let t : Points R c L K b := ⟨w.left,rfl⟩
    refine ⟨b,s,t,rfl,rfl,composition R c L K L b s (inverse R c L K b t),?_⟩
    exact ContactOriginalIsomPointTorsor318.cancel_difference R c L K b s t
/-- Restriction of the relation is produced through exact scheme
projection equality. It covers arbitrary whole site arrows. -/
lemma restrict {T U : Over Q} (f : U ⟶ T) {z w : T ⟶ P}
    (h : Related R c L K T z w) : Related R c L K U (f ≫ z) (f ≫ w) := by
  apply (iff_projection R c L K U _ _).mpr
  rw [Category.assoc,Category.assoc,(iff_projection R c L K T z w).mp h]
end ContactOriginalIsomOrbitRelation318
