module
public import ActualQuadricScaling318
public section
noncomputable section
namespace ActualSingularResidueFiber318
open QuadricCRTAssembly318 ActualCoordinateLiftFiber318 ActualPrimitiveResidueLiftSet318
open ActualQuadricScaling318
set_option maxHeartbeats 24000000

/-- The actual origin fiber at the original prime p inside the
original quadric modulo p^2*m. -/
@[expose] def SingularResidues (κ : ℤ) (m p : ℕ) :=
  {y : Quadric (κ:ZMod (p*(m*p))) //
    mapCoordinates (ActualResidueDigitEquiv318.reduce p (m*p)) y.1=((0,0),(0,0),0)}
/-- These are ALL coordinate lifts of the lower-level quadric. There
is no equation modulo m*p imposed on z itself. -/
@[expose] def LowerQuadricPreimage (κ : ℤ) (m p : ℕ) :=
  {z : Coordinates (ZMod (m*p)) //
    equation (κ:ZMod m) (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) z)=0}

@[expose] def actual_singular_equiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] :
    SingularResidues κ m p ≃ LowerQuadricPreimage κ m p := by
  let e := coordinateFiberEquiv p (m*p) (((0,0),(0,0),0):Coordinates (ZMod p))
  refine {
    toFun := fun y => ⟨e.symm ⟨y.1.1,y.2⟩,?_⟩
    invFun := fun z => ⟨⟨(e z.1).1,?_⟩,(e z.1).2⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (actual_singular_test κ m p _).mp
    change equation (κ:ZMod (p*(m*p))) (e (e.symm ⟨y.1.1,y.2⟩)).1=0
    rw [congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1,y.2⟩)]
    exact y.1.2
  · exact (actual_singular_test κ m p z.1).mpr z.2
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1,y.2⟩)
  · intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.1

/-- The unrestricted last digits of a singular lift are genuine
independent original coordinates, not an asserted multiplicity. -/
@[expose] def lower_preimage_equiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] :
    LowerQuadricPreimage κ m p ≃
      (Quadric (κ:ZMod m) × Coordinates (ZMod p)) := by
  let e := coordinateFiberEquiv m p
  refine {
    toFun := fun z => (⟨mapCoordinates (ActualResidueDigitEquiv318.reduce m p) z.1,z.2⟩,
      (e (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) z.1)).symm ⟨z.1,rfl⟩)
    invFun := fun v => ⟨(e v.1.1 v.2).1,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [(e v.1.1 v.2).2]
    exact v.1.2
  · intro z
    apply Subtype.ext
    exact congrArg Subtype.val ((e _).apply_symm_apply ⟨z.1,rfl⟩)
  · rintro ⟨x,h⟩
    apply Prod.ext
    · apply Subtype.ext
      exact (e x.1 h).2
    · exact (e x.1).symm_apply_apply h

end ActualSingularResidueFiber318
