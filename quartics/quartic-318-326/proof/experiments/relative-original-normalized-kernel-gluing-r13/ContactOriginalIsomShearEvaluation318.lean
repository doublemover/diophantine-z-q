module
public import ContactOriginalIsomShearMaps318
public section
noncomputable section
namespace ContactOriginalIsomShearEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactIsomParameterProduct318 ContactOriginalIsomShearMaps318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- Exact evaluation of the actual shear map on ALL whole parameter pairs. -/
lemma shear_evaluation (a : Points R c L L b) (z : Points R c L K b) :
    pairMap R c L L L K b a z ≫ shear R c L K=
      pairMap R c L K L K b (ContactOriginalIsomPointOperations318.composition R c L L K b a z) z := by
  apply pullback.hom_ext
  · rw [Category.assoc,shear_fst,pairMap_fst]
    exact ContactOriginalIsomGeometricComposition318.evaluation R c L L K b a z
  · rw [Category.assoc,shear_snd,pairMap_snd,pairMap_snd]
lemma difference_evaluation (z w : Points R c L K b) :
    pairMap R c L K L K b z w ≫ differenceMap R c L K=
      ContactOriginalIsomGeometricComposition318.pairMap R c L K L b z
        (ContactOriginalIsomPointOperations318.inverse R c L K b w) := by
  apply pullback.hom_ext
  · rw [Category.assoc,difference_fst,pairMap_fst,
      ContactOriginalIsomGeometricComposition318.pairMap,pullback.lift_fst]
  · rw [Category.assoc,difference_snd,←Category.assoc,pairMap_snd,
      ContactOriginalIsomGeometricComposition318.pairMap,pullback.lift_snd]
    exact ContactOriginalIsomGeometricInverse318.inversion_evaluation R c L K b w
/-- Recover the literal automorphism z composed with w inverse, retaining
both full isomorphisms, rather than only their equality-fiber base point. -/
lemma unshear_evaluation (z w : Points R c L K b) :
    pairMap R c L K L K b z w ≫ unshear R c L K=
      pairMap R c L L L K b
        (ContactOriginalIsomPointOperations318.composition R c L K L b z
          (ContactOriginalIsomPointOperations318.inverse R c L K b w)) w := by
  apply pullback.hom_ext
  · rw [Category.assoc,unshear_fst,pairMap_fst,difference,←Category.assoc,difference_evaluation]
    exact ContactOriginalIsomGeometricComposition318.evaluation R c L K L b z
      (ContactOriginalIsomPointOperations318.inverse R c L K b w)
  · rw [Category.assoc,unshear_snd,pairMap_snd,pairMap_snd]
end ContactOriginalIsomShearEvaluation318
