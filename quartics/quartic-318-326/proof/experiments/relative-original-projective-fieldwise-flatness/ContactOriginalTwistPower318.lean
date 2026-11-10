module
public import BinaryFramedPowerComparison318
public import ContactOriginalPositiveTwistHOne318
public import LineSheafTensorPower318
public section
noncomputable section
namespace ContactOriginalTwistPower318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The forward entry extracted from the ACTUAL old clutched frames is
exactly its original unit T^d, by the original coefficient relation. -/
lemma forward (d : ℤ) :
    (LineFrameCocycle318.cocycle (line c d).object (line c d).opens (line c d).frame).transition
      ⟨false⟩ ⟨true⟩ = transitionUnit c d := by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame (line c d).object (finiteOpen c)
      (finiteFrame c d).symm _ inf_le_left).symm
    (OpenLineFrameCoordinates318.frame (line c d).object (infinityOpen c)
      (infinityFrame c d).symm _ inf_le_right 1) = (transitionUnit c d).val
  rw [ContactOriginalTwistTransition318.inverse_relation,LinearEquiv.symm_apply_apply,one_mul]

lemma unit_power (n : ℕ) : transitionUnit c (n : ℤ) = transitionUnit c 1 ^ n := by
  induction n with
  | zero =>
    apply Units.ext
    simp only [Nat.cast_zero,pow_zero,Units.val_one,transitionUnit_val,LaurentPolynomial.T_zero,map_one]
  | succ n ih =>
    rw [Nat.cast_succ,transitionUnit_add,ih,pow_succ]

/-- The actual clutched T^n line is isomorphic to the genuine nth iterated
tensor power of the SINGLE unchanged original positive line. This is an
object-level reconstruction, not just equality of dimensions or classes. -/
def powerIso (n : ℕ) : (LineSheafTensorPower318.line (line c 1) n).object ≅ (line c (n : ℤ)).object :=
  BinaryFramedPowerComparison318.iso (line c 1).object (line c (n : ℤ)).object
    (finiteOpen c) (infinityOpen c) (line c 1).frame (line c (n : ℤ)).frame n (cover c)
    (by rw [forward,forward,unit_power])

/-- The original arbitrary line is unchanged on the left tensor factor. -/
def twistedPowerIso (L : Line (ContactProjectiveModel318.model c)) (n : ℕ) :
    (LineSheafTensor318.line L (LineSheafTensorPower318.line (line c 1) n)).object ≅
      (twist c L (n : ℤ)).object :=
  TensorSheafFunctor318.congr (Iso.refl L.object) (powerIso c n)

/-- Retains the exact original reconstructed cocycle comparison, not an
arbitrary isomorphism selected after passing to line classes. -/
lemma class_power (n : ℕ) : classOf (line c (n : ℤ)) = classOf (line c 1) ^ n :=
  (classOf_eq (powerIso c n)).symm.trans (LineSheafTensorPower318.classOf_power (line c 1) n)
end ContactOriginalTwistPower318
