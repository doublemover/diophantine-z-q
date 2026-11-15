module
public import ContactOriginalIsomShearEvaluation318
public section
noncomputable section
namespace ContactOriginalIsomShearInverse318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactIsomParameterProduct318 ContactOriginalIsomShearMaps318 ContactOriginalIsomShearEvaluation318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
lemma hom_inv : shear R c L K ≫ unshear R c L K=𝟙 (source R c L K) := by
  let b := base R c L L L K
  let a := first R c L L L K
  let z := second R c L L L K
  have hu : pairMap R c L L L K b a z=𝟙 (source R c L K) := universal_pair R c L L L K
  calc
    _ = (pairMap R c L L L K b a z ≫ shear R c L K) ≫ unshear R c L K := by
      rw [hu,Category.id_comp]
    _ = pairMap R c L K L K b
        (ContactOriginalIsomPointOperations318.composition R c L L K b a z) z ≫ unshear R c L K := by
      rw [shear_evaluation]
    _ = pairMap R c L L L K b
        (ContactOriginalIsomPointOperations318.composition R c L K L b
          (ContactOriginalIsomPointOperations318.composition R c L L K b a z)
          (ContactOriginalIsomPointOperations318.inverse R c L K b z)) z :=
      unshear_evaluation R c L K b _ z
    _ = pairMap R c L L L K b a z := by rw [ContactOriginalIsomPointTorsor318.cancel_action]
    _ = _ := hu
lemma inv_hom : unshear R c L K ≫ shear R c L K=𝟙 (target R c L K) := by
  let b := base R c L K L K
  let z := first R c L K L K
  let w := second R c L K L K
  have hu : pairMap R c L K L K b z w=𝟙 (target R c L K) := universal_pair R c L K L K
  calc
    _ = (pairMap R c L K L K b z w ≫ unshear R c L K) ≫ shear R c L K := by
      rw [hu,Category.id_comp]
    _ = pairMap R c L L L K b
        (ContactOriginalIsomPointOperations318.composition R c L K L b z
          (ContactOriginalIsomPointOperations318.inverse R c L K b w)) w ≫ shear R c L K := by
      rw [unshear_evaluation]
    _ = pairMap R c L K L K b
        (ContactOriginalIsomPointOperations318.composition R c L L K b
          (ContactOriginalIsomPointOperations318.composition R c L K L b z
            (ContactOriginalIsomPointOperations318.inverse R c L K b w)) w) w :=
      shear_evaluation R c L K b _ w
    _ = pairMap R c L K L K b z w := by rw [ContactOriginalIsomPointTorsor318.cancel_difference]
    _ = _ := hu
end ContactOriginalIsomShearInverse318
