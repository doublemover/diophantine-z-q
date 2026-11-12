module
public import ContactOriginalIsomGeometricLaws318
public section
noncomputable section
namespace ContactOriginalIsomGeometricAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomGeometricComposition318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M N : Line (curve R c))
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- The point whose underlying map is LITERALLY the produced geometric
composition of the two parameter maps. -/
@[expose] def composed (z : Points R c L K b) (w : Points R c K M b) : Points R c L M b :=
  ⟨pairMap R c L K M b z w ≫ composition R c L K M,by
    rw [Category.assoc,composition_over,pairMap_base]⟩
lemma composed_eq (z : Points R c L K b) (w : Points R c K M b) :
    composed R c L K M b z w=ContactOriginalIsomPointOperations318.composition R c L K M b z w := by
  apply Subtype.ext
  exact evaluation R c L K M b z w
/-- Associativity of the actual geometric operations on every whole
scheme, preserving the SAME intermediate original line modules. -/
lemma on_test (z : Points R c L K b) (w : Points R c K M b) (v : Points R c M N b) :
    pairMap R c L M N b (composed R c L K M b z w) v ≫ composition R c L M N=
      pairMap R c L K N b z (composed R c K M N b w v) ≫ composition R c L K N := by
  rw [composed_eq,composed_eq,evaluation,evaluation]
  exact congrArg Subtype.val (ContactOriginalIsomPointLaws318.associativity R c L K M N b z w v)
/-- The literal whole triple parameter, not a test restricted to fields. -/
abbrev triples := pullback (base R c L K M) (q M N)
@[expose] def tripleBase : triples R c L K M N ⟶ Spec R :=
  pullback.fst (base R c L K M) (q M N) ≫ base R c L K M
@[expose] def tripleFirst : Points R c L K (tripleBase R c L K M N) :=
  ⟨pullback.fst (base R c L K M) (q M N) ≫ (first R c L K M).val,by
    rw [Category.assoc,(first R c L K M).property]; rfl⟩
@[expose] def tripleSecond : Points R c K M (tripleBase R c L K M N) :=
  ⟨pullback.fst (base R c L K M) (q M N) ≫ (second R c L K M).val,by
    rw [Category.assoc,(second R c L K M).property]; rfl⟩
@[expose] def tripleThird : Points R c M N (tripleBase R c L K M N) :=
  ⟨pullback.snd (base R c L K M) (q M N),(pullback.condition).symm⟩
@[expose] def leftAssociated : triples R c L K M N ⟶ P L N :=
  pairMap R c L M N (tripleBase R c L K M N)
    (composed R c L K M (tripleBase R c L K M N)
      (tripleFirst R c L K M N) (tripleSecond R c L K M N))
    (tripleThird R c L K M N) ≫ composition R c L M N
@[expose] def rightAssociated : triples R c L K M N ⟶ P L N :=
  pairMap R c L K N (tripleBase R c L K M N) (tripleFirst R c L K M N)
    (composed R c K M N (tripleBase R c L K M N)
      (tripleSecond R c L K M N) (tripleThird R c L K M N)) ≫ composition R c L K N
/-- Equality of actual scheme morphisms out of the complete triple
fiber product. No field-point detection or quotient effectiveness premise. -/
lemma associativity : leftAssociated R c L K M N=rightAssociated R c L K M N :=
  on_test R c L K M N (tripleBase R c L K M N)
    (tripleFirst R c L K M N) (tripleSecond R c L K M N) (tripleThird R c L K M N)
end ContactOriginalIsomGeometricAssociativity318
