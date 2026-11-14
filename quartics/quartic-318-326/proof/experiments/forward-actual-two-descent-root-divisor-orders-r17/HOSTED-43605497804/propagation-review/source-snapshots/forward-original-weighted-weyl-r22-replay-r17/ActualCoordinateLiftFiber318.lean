module
public import ActualResidueDigitEquiv318
public section
noncomputable section
namespace ActualCoordinateLiftFiber318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualQuadricTaylor318
set_option maxHeartbeats 20000000

@[expose] def BaseFiber (m p : ℕ) (x : Coordinates (ZMod m)) :=
  {y : Coordinates (ZMod (m*p)) // mapCoordinates (ActualResidueDigitEquiv318.reduce m p) y=x}

/-- Concrete product of the FIVE scalar base-m fiber equivalences.
Every ambient coordinate tuple above the original x is reached exactly
once by actual p-digits, without a coprime-modulus assumption. -/
@[expose] def coordinateFiberEquiv (m p : ℕ) [NeZero m] [NeZero p]
    (x : Coordinates (ZMod m)) : Coordinates (ZMod p) ≃ BaseFiber m p x := by
  let e := ActualResidueDigitEquiv318.fiberEquiv m p
  let d := ActualResidueDigitEquiv318.digitEquiv m p
  refine {
    toFun := fun h => ⟨(((e x.1.1 h.1.1).1,(e x.1.2 h.1.2).1),
      ((e x.2.1.1 h.2.1.1).1,(e x.2.1.2 h.2.1.2).1),(e x.2.2 h.2.2).1),?_⟩
    invFun := fun y => (((d y.1.1.1).2,(d y.1.1.2).2),
      ((d y.1.2.1.1).2,(d y.1.2.1.2).2),(d y.1.2.2).2)
    left_inv := ?_
    right_inv := ?_ }
  · exact Prod.ext (Prod.ext (e x.1.1 h.1.1).2 (e x.1.2 h.1.2).2)
      (Prod.ext (Prod.ext (e x.2.1.1 h.2.1.1).2 (e x.2.1.2 h.2.1.2).2)
        (e x.2.2 h.2.2).2)
  · intro h
    exact Prod.ext (Prod.ext ((e x.1.1).symm_apply_apply h.1.1) ((e x.1.2).symm_apply_apply h.1.2))
      (Prod.ext (Prod.ext ((e x.2.1.1).symm_apply_apply h.2.1.1)
        ((e x.2.1.2).symm_apply_apply h.2.1.2)) ((e x.2.2).symm_apply_apply h.2.2))
  · intro y
    have ha := congrArg (fun z : Coordinates (ZMod m) => z.1.1) y.2
    have hb := congrArg (fun z : Coordinates (ZMod m) => z.1.2) y.2
    have hc := congrArg (fun z : Coordinates (ZMod m) => z.2.1.1) y.2
    have hd := congrArg (fun z : Coordinates (ZMod m) => z.2.1.2) y.2
    have hw := congrArg (fun z : Coordinates (ZMod m) => z.2.2) y.2
    apply Subtype.ext
    exact Prod.ext
      (Prod.ext (congrArg Subtype.val ((e x.1.1).apply_symm_apply ⟨y.1.1.1,ha⟩))
        (congrArg Subtype.val ((e x.1.2).apply_symm_apply ⟨y.1.1.2,hb⟩)))
      (Prod.ext
        (Prod.ext (congrArg Subtype.val ((e x.2.1.1).apply_symm_apply ⟨y.1.2.1.1,hc⟩))
          (congrArg Subtype.val ((e x.2.1.2).apply_symm_apply ⟨y.1.2.1.2,hd⟩)))
        (congrArg Subtype.val ((e x.2.2).apply_symm_apply ⟨y.1.2.2,hw⟩)))

/-- The ambient residue reconstruction is exactly reduction of the
literal INTEGER translate used by the p^4 digit-count theorem. -/
lemma actual_integer_lift_formula (m p : ℕ) [NeZero m] [NeZero p]
    (x : Coordinates (ZMod m)) (h : Coordinates (ZMod p)) :
    (coordinateFiberEquiv m p x h).1=
      mapCoordinates (Int.castRingHom (ZMod (m*p)))
        (translate (digits m x) (digits p h) (m:ℤ)) := by
  simp only [coordinateFiberEquiv,ActualResidueDigitEquiv318.fiberEquiv,
    ActualResidueDigitEquiv318.digitEquiv,mapCoordinates,translate,digits,
    Int.castRingHom_apply,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul]

end ActualCoordinateLiftFiber318
