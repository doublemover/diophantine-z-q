module
public import OriginalCasselsNativeDyadicIsogeny318
import all OriginalCasselsDyadicXClass318
import all OriginalCasselsLiteralIsogenyPoint318
public section

noncomputable section

namespace OriginalCasselsLiteralRangeFinite318

open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyAddition318
open OriginalSelectedCasselsParity318 ActualTwoDescentEllipticModel318
open OriginalCasselsDyadicXClass318 OriginalCasselsDyadicClassUpper318
open OriginalCasselsTargetClassChord318 ActualTwoDescentSquareClassQuotient318

section Field
variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- Kernel/range equality for the literal map, before imposing any
assumption that a local quotient is finite. -/
theorem target_class_one_iff_literal_range (n : F) (hn : n ≠ 0) (P : TargetPoint n) :
    targetClass P=1 ↔ P ∈ (literalHom (literal_addition n hn)).range :=
  target_class_one_iff_unbounded_range
    (literalHom (literal_addition n hn)) (literal_affine n hn)
    (literal_kernel_point n hn) P

/-- Isomorphism of the actual quotient with the actual target x-class
image. It applies uniformly over all fields in the literal point ABI. -/
def literalQuotientEquiv (n : F) (hn : n ≠ 0) :
    TargetPoint n ⧸ (literalHom (literal_addition n hn)).range ≃+
      ↥(AddMonoidHom.range (G := TargetPoint n) (N := Additive (SquareClass F))
        (xClassHom (actual_target_class_product n hn))) := by
  let XC : TargetPoint n →+ Additive (SquareClass F) :=
    xClassHom (actual_target_class_product n hn)
  have hk : AddMonoidHom.ker (G := TargetPoint n) (M := Additive (SquareClass F)) XC =
      (literalHom (literal_addition n hn)).range := by
    ext P
    change targetClass P=1 ↔ P ∈ (literalHom (literal_addition n hn)).range
    exact target_class_one_iff_literal_range n hn P
  have e := QuotientAddGroup.quotientKerEquivRange
    (G := TargetPoint n) (H := Additive (SquareClass F)) XC
  let swap : TargetPoint n ⧸ (literalHom (literal_addition n hn)).range ≃+
      TargetPoint n ⧸ XC.ker := QuotientAddGroup.quotientAddEquivOfEq hk.symm
  exact swap.trans e

end Field

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq (ℚ_[2]) := Classical.decEq _

private theorem finite_xclass_dyadic (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    Finite ↥(AddMonoidHom.range (G := TargetPoint (n:ℚ_[2]))
      (N := Additive (SquareClass ℚ_[2]))
      (xClassHom (actual_target_class_product (n:ℚ_[2])
        (Nat.cast_ne_zero.mpr hn.ne')))) := by
  obtain ⟨P₅,h5⟩ := actual_class_five_witness n hn hr
  let h : TargetPoint (n:ℚ_[2]) →+ Additive (SquareClass ℚ_[2]) :=
    xClassHom (actual_target_class_product (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))
  let R : AddSubgroup (Additive (SquareClass ℚ_[2])) :=
    AddMonoidHom.range (G := TargetPoint (n:ℚ_[2])) (N := Additive (SquareClass ℚ_[2])) h
  change Finite ↥R
  let image (P : TargetPoint (n:ℚ_[2])) : ↥R := ⟨h P,⟨P,rfl⟩⟩
  let f : Bool → ↥R := fun b => Bool.rec (motive := fun _ => ↥R) (image 0) (image P₅) b
  apply Finite.of_surjective f
  rintro ⟨a,P,rfl⟩
  rcases actual_dyadic_class_upper n hn hr P with hz|hf
  · refine ⟨false,Subtype.ext ?_⟩
    change (1 : SquareClass ℚ_[2])=targetClass P
    exact hz.symm
  · refine ⟨true,Subtype.ext ?_⟩
    change targetClass P₅=targetClass P
    exact h5.trans hf.symm

theorem literal_dyadic_quotient_finite (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    Finite (TargetPoint (n:ℚ_[2]) ⧸
      (literalHom (literal_addition (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))).range) := by
  letI := finite_xclass_dyadic n hn hr
  exact Finite.of_equiv _ (literalQuotientEquiv (n:ℚ_[2])
    (Nat.cast_ne_zero.mpr hn.ne')).symm.toEquiv

/-- Genuine local isogeny on the original Q₂ points for the selected
residue, with no supplied finiteness, count, point map, or chord law. -/
def localDyadicIsogeny (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    LocalIsogeny (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') :=
  OriginalCasselsNativeDyadicIsogeny318.dyadic n hn (literal_dyadic_quotient_finite n hn hr)

theorem local_dyadic_cokernel_card (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    (localDyadicIsogeny n hn hr).cokernelCard=2 :=
  OriginalCasselsNativeDyadicIsogeny318.dyadic_cokernel_card n hn hr
    (literal_dyadic_quotient_finite n hn hr)

end OriginalCasselsLiteralRangeFinite318

#print axioms OriginalCasselsLiteralRangeFinite318.target_class_one_iff_literal_range
#print axioms OriginalCasselsLiteralRangeFinite318.literal_dyadic_quotient_finite
#print axioms OriginalCasselsLiteralRangeFinite318.local_dyadic_cokernel_card
