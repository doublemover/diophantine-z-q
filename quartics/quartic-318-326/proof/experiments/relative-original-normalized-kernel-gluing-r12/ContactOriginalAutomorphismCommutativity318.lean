module
public import ContactOriginalIsomTorsorOver318
public section
noncomputable section
namespace ContactOriginalAutomorphismCommutativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L L
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- The full stabilizer points are units of the WHOLE original family
ring. Identification of this ring with the base ring is not assumed. -/
@[expose] def values : Points R c L L b ≃ Γ(pullback p b,⊤)ˣ :=
  (ContactWholeIsomPointEquivalence318.equivalence R c L L T b).trans
    (OriginalLineAutomorphismUnits318.automorphisms (LineSheafPullback318.line (pullback.fst p b) L))
lemma point_comm (z w : Points R c L L b) :
    ContactOriginalIsomPointOperations318.composition R c L L L b z w=
      ContactOriginalIsomPointOperations318.composition R c L L L b w z := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L L T b).injective
  rw [ContactOriginalIsomPointOperations318.recover_composition,
    ContactOriginalIsomPointOperations318.recover_composition]
  apply (OriginalLineAutomorphismUnits318.automorphisms
    (LineSheafPullback318.line (pullback.fst p b) L)).injective
  change OriginalLineAutomorphismUnits318.value _ (_ ≪≫ _)=
    OriginalLineAutomorphismUnits318.value _ (_ ≪≫ _)
  rw [OriginalLineAutomorphismUnits318.value_multiplication,
    OriginalLineAutomorphismUnits318.value_multiplication,mul_comm]
@[expose] def flip : ContactIsomParameterProduct318.parameter R c L L L L ⟶
    ContactIsomParameterProduct318.parameter R c L L L L :=
  pullback.lift (pullback.snd q q) (pullback.fst q q) pullback.condition.symm
/-- The actual automorphism-parameter multiplication is commutative as
a SCHEME morphism, not merely at geometric points or after quotienting. -/
lemma geometric_comm : flip R c L ≫ ContactOriginalIsomGeometricComposition318.composition R c L L L=
    ContactOriginalIsomGeometricComposition318.composition R c L L L := by
  let b := ContactIsomParameterProduct318.base R c L L L L
  let z := ContactIsomParameterProduct318.first R c L L L L
  let w := ContactIsomParameterProduct318.second R c L L L L
  have hu : ContactOriginalIsomGeometricComposition318.pairMap R c L L L b z w=𝟙 _ :=
    ContactIsomParameterProduct318.universal_pair R c L L L L
  have hf : flip R c L=ContactOriginalIsomGeometricComposition318.pairMap R c L L L b w z := rfl
  calc
    _ = (ContactOriginalIsomPointOperations318.composition R c L L L b w z).val := by
      rw [hf,ContactOriginalIsomGeometricComposition318.evaluation]
    _ = (ContactOriginalIsomPointOperations318.composition R c L L L b z w).val :=
      congrArg Subtype.val (point_comm R c L b w z)
    _ = ContactOriginalIsomGeometricComposition318.pairMap R c L L L b z w ≫
        ContactOriginalIsomGeometricComposition318.composition R c L L L :=
      (ContactOriginalIsomGeometricComposition318.evaluation R c L L L b z w).symm
    _ = _ := by rw [hu,Category.id_comp]
end ContactOriginalAutomorphismCommutativity318
