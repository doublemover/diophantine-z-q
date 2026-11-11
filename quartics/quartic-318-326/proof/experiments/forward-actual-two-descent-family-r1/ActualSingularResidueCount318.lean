module
public import ActualSingularResidueFiber318
public section
noncomputable section
namespace ActualSingularResidueCount318
open QuadricCRTAssembly318 ActualPrimitivePrimePower318 ActualSingularResidueFiber318
open ActualQuadricScaling318
set_option maxHeartbeats 24000000

lemma actual_five_digit_card (p : ℕ) [NeZero p] : Nat.card (Coordinates (ZMod p))=p^5 := by
  simp only [Coordinates,Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card]
  ring

/-- Exact count of ALL singular original residues. The p^5 factor
is the constructed full five-coordinate last-digit fiber, while the
lower factor is the actual whole original quadric modulo m. -/
theorem actual_singular_count (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] :
    Nat.card (SingularResidues κ m p)=Nat.card (Quadric (κ:ZMod m))*p^5 := by
  rw [Nat.card_congr (actual_singular_equiv κ m p),
    Nat.card_congr (lower_preimage_equiv κ m p),Nat.card_prod,actual_five_digit_card]

/-- The singular fiber is exactly the complement of primitivity at
the original prime inside this SAME ambient original quadric. -/
@[expose] def singularComplementEquiv (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] :
    SingularResidues κ m p ≃
      {y : Quadric (κ:ZMod (p*(m*p))) // ¬IsPrimitive κ (p*(m*p)) p y} where
  toFun y := ⟨y.1,by
    change ¬mapCoordinates (Int.castRingHom (ZMod p))
      (ActualOriginalModularLift318.digits (p*(m*p)) y.1.1)≠_
    rw [←reduce_integer_digits p (m*p)]
    exact not_not.mpr y.2⟩
  invFun y := ⟨y.1,by
    have hh := y.2
    change ¬mapCoordinates (Int.castRingHom (ZMod p))
      (ActualOriginalModularLift318.digits (p*(m*p)) y.1.1)≠_ at hh
    rw [←reduce_integer_digits p (m*p)] at hh
    exact not_not.mp hh⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Primitive and singular points exhaust the original residue set
without overlap; no abstract recurrence is supplied as an assumption. -/
theorem actual_whole_quadric_split (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p] :
    Nat.card (Quadric (κ:ZMod (p*(m*p))))=
      Nat.card (PrimitiveResidues κ (p*(m*p)) p)+Nat.card (Quadric (κ:ZMod m))*p^5 := by
  classical
  have hh := Nat.card_congr (Equiv.sumCompl (IsPrimitive κ (p*(m*p)) p))
  rw [Nat.card_sum] at hh
  change Nat.card (PrimitiveResidues κ (p*(m*p)) p)+
    Nat.card {y : Quadric (κ:ZMod (p*(m*p))) // ¬IsPrimitive κ (p*(m*p)) p y}=_ at hh
  rw [←Nat.card_congr (singularComplementEquiv κ m p),actual_singular_count] at hh
  exact hh.symm

end ActualSingularResidueCount318
