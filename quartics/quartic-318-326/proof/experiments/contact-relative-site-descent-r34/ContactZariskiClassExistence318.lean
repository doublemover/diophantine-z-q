module
public import OriginalOpenTestNaturality318
public section
noncomputable section
namespace ContactZariskiClassExistence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RelativeLineClassBaseChange318 OriginalOpenFamilyTest318 OriginalOpenTestNaturality318
open ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T : Scheme} (b : T ⟶ FieldBase t) {ι : Type} (U : ι → T.Opens)
  (hc : (⊤ : T.Opens) ≤ iSup U) (c : ∀ i, TestClass (q t) ((U i).ι ≫ b))
  (matching : ∀ i j,
    testMap (q t) ((U i).ι ≫ b) ((U i ⊓ U j).ι ≫ b)
        (T.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) (test_path b inf_le_left) (c i) =
      testMap (q t) ((U j).ι ≫ b) ((U i ⊓ U j).ι ≫ b)
        (T.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)) (test_path b inf_le_right) (c j))

include hc matching in
/-- Every standard matching family of original Contact relative classes
on an arbitrary Zariski open cover has an original global class. Neither
finiteness nor affine/reduced hypotheses are imposed on the test or opens. -/
theorem exists_class : ∃ d : TestClass (q t) b,
    ∀ i, testMap (q t) b ((U i).ι ≫ b) (U i).ι rfl d = c i := by
  let c' := fun i => OriginalOpenRelativeClasses318.equivalence (q t) b (U i) (c i)
  have hm : ∀ i j,
      OriginalPointedOpenFamily318.classMap (q t) b (show U i ⊓ U j ≤ U i from inf_le_left) (c' i) =
        OriginalPointedOpenFamily318.classMap (q t) b (show U i ⊓ U j ≤ U j from inf_le_right) (c' j) := by
    intro i j
    rw [OriginalOpenTestNaturality318.class_natural,OriginalOpenTestNaturality318.class_natural,
      matching i j]
  obtain ⟨d,hd⟩ := OriginalOpenClassGluing318.effective (q t) b (e t) (section_eq t) U hc c'
    (fun V => OriginalOpenFamilyTest318.evaluation_bijective (q t) b V (e t) (section_eq t)) hm
  refine ⟨d,fun i => ?_⟩
  apply (OriginalOpenRelativeClasses318.equivalence (q t) b (U i)).injective
  rw [OriginalOpenRelativeClasses318.restriction_eq]
  exact hd i
end ContactZariskiClassExistence318
