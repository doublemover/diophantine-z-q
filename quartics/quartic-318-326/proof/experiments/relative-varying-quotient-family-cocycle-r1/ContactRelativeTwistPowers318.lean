module
public import ContactRelativeGeometricVanishing318
public import BinaryFramedPowerComparison318
public import LineSheafTensorPower318
public section
noncomputable section
namespace ContactRelativeTwistPowers318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactRelativeGeometricTwist318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

lemma forward (d : ℤ) :
    (LineFrameCocycle318.cocycle (line R c d).object (line R c d).opens (line R c d).frame).transition
      ⟨false⟩ ⟨true⟩ = transition R c d := by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame (line R c d).object (finiteOpen R c)
    (finiteFrame R c d).symm _ inf_le_left).symm
      (OpenLineFrameCoordinates318.frame (line R c d).object (infinityOpen R c)
        (infinityFrame R c d).symm _ inf_le_right 1) = (transition R c d).val
  rw [frame_relation,LinearEquiv.symm_apply_apply,one_mul]

lemma transition_add (d e : ℤ) : transition R c (d+e) = transition R c d * transition R c e := by
  apply Units.ext
  change scalar R c (LaurentPolynomial.T (d+e)) = scalar R c (LaurentPolynomial.T d) * scalar R c (LaurentPolynomial.T e)
  rw [LaurentPolynomial.T_add,map_mul]

lemma transition_power (n : ℕ) : transition R c (n : ℤ) = transition R c 1 ^ n := by
  induction n with
  | zero =>
    apply Units.ext
    change scalar R c (LaurentPolynomial.T (0 : ℤ)) = 1
    rw [LaurentPolynomial.T_zero,map_one]
  | succ n ih => rw [Nat.cast_succ,transition_add,ih,pow_succ]

/-- The geometric T^n twist is the genuine nth power of ONE fixed
relative line, by its exact original cocycle and reconstructed maps. -/
@[expose] def powerIso (n : ℕ) :
    (LineSheafTensorPower318.line (line R c 1) n).object ≅ (line R c (n : ℤ)).object :=
  BinaryFramedPowerComparison318.iso (line R c 1).object (line R c (n : ℤ)).object
    (finiteOpen R c) (infinityOpen R c) (line R c 1).frame (line R c (n : ℤ)).frame n (cover R c)
    (by rw [forward,forward,transition_power])

@[expose] def twistedPowerIso (L : Line (curve R c)) (n : ℕ) :
    (LineSheafTensor318.line L (LineSheafTensorPower318.line (line R c 1) n)).object ≅
      (twist R c L (n : ℤ)).object :=
  TensorSheafFunctor318.congr (Iso.refl L.object) (powerIso R c n)
end ContactRelativeTwistPowers318
