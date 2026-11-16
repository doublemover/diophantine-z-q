module
public import ContactOriginalIsomGeometricInverse318
public section
noncomputable section
namespace ContactOriginalIsomGeometricComposition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M : Line (curve R c))
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
/-- The literal fiber product of the SAME two original parameters. -/
abbrev pairs := pullback (q L K) (q K M)
@[expose] def base : pairs R c L K M ⟶ Spec R := pullback.fst (q L K) (q K M) ≫ q L K
@[expose] def first : Points R c L K (base R c L K M) := ⟨pullback.fst _ _,rfl⟩
@[expose] def second : Points R c K M (base R c L K M) :=
  ⟨pullback.snd _ _,(pullback.condition).symm⟩
/-- Actual geometric composition classifies the composition of the full
native pullbacks of both universal original isomorphisms. -/
@[expose] def composition : pairs R c L K M ⟶ P L M :=
  (ContactOriginalIsomPointOperations318.composition R c L K M (base R c L K M)
    (first R c L K M) (second R c L K M)).val
lemma composition_over : composition R c L K M ≫ q L M=base R c L K M :=
  (ContactOriginalIsomPointOperations318.composition R c L K M (base R c L K M)
    (first R c L K M) (second R c L K M)).property
/-- The universal geometric composition recovers EXACTLY the composition
of the two literal native pullbacks of the original universal isomorphisms. -/
lemma composition_recovers :
    ContactWholeIsomPointEquivalence318.equivalence R c L M (pairs R c L K M)
      (base R c L K M) ⟨composition R c L K M,composition_over R c L K M⟩=
    pullIso R c L K (q L K) (base R c L K M) (first R c L K M).val
      (first R c L K M).property (ContactUniversalOriginalIsom318.universal R c L K) ≪≫
    pullIso R c K M (q K M) (base R c L K M) (second R c L K M).val
      (second R c L K M).property (ContactUniversalOriginalIsom318.universal R c K M) := by
  simp only [ContactUniversalOriginalIsom318.pullback]
  exact ContactOriginalIsomPointOperations318.recover_composition R c L K M
    (base R c L K M) (first R c L K M) (second R c L K M)
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
@[expose] def pairMap (z : Points R c L K b) (w : Points R c K M b) :
    T ⟶ pairs R c L K M := pullback.lift z.val w.val (z.property.trans w.property.symm)
lemma pairMap_base (z : Points R c L K b) (w : Points R c K M b) :
    pairMap R c L K M b z w ≫ base R c L K M=b := by
  rw [base,←Category.assoc,pairMap,pullback.lift_fst,z.property]
/-- Every whole-test evaluation is the full original isomorphism
composition, not an abstract operation on equivalence classes. -/
lemma evaluation (z : Points R c L K b) (w : Points R c K M b) :
    pairMap R c L K M b z w ≫ composition R c L K M=
      (ContactOriginalIsomPointOperations318.composition R c L K M b z w).val := by
  have h := ContactOriginalIsomOperationsNaturality318.composition R c L K M
    (base R c L K M) b (pairMap R c L K M b z w) (pairMap_base R c L K M b z w)
    (first R c L K M) (second R c L K M)
  have hz : pointMap R c L K (base R c L K M) b (pairMap R c L K M b z w)
      (pairMap_base R c L K M b z w) (first R c L K M)=z := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  have hw : pointMap R c K M (base R c L K M) b (pairMap R c L K M b z w)
      (pairMap_base R c L K M b z w) (second R c L K M)=w := by
    apply Subtype.ext
    exact pullback.lift_snd _ _ _
  rw [hz,hw] at h
  exact congrArg Subtype.val h
end ContactOriginalIsomGeometricComposition318
