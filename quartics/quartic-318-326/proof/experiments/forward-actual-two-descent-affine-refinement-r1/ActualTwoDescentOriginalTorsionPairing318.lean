module
public import ActualTwoDescentBinarySymplectic318
public section
noncomputable section
namespace ActualTwoDescentOriginalTorsionPairing318
open ActualTwoDescentSquareOneBinary318 ActualTwoDescentBinarySymplectic318
open ActualTwoDescentFieldTorsionSignEquivalence318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldActualGaloisCohomology318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local instance : DecidableEq Qbar := Classical.decEq _

/-- Coordinates of the original geometric E[2], with the original root
ordering. Both forward and inverse maps are the already constructed signs. -/
def torsionBinaryMulEquiv (n : F) (hn : n ≠ 0) :
    Multiplicative (closedTwoTorsion n) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  (torsionSignEquiv n hn).trans (MulEquiv.prodCongr squareOneBinaryEquiv squareOneBinaryEquiv)

def torsionBinaryEquiv (n : F) (hn : n ≠ 0) : closedTwoTorsion n ≃+ BinaryPlane where
  toFun x := ((torsionBinaryMulEquiv n hn (Multiplicative.ofAdd x)).1.toAdd,
    (torsionBinaryMulEquiv n hn (Multiplicative.ofAdd x)).2.toAdd)
  invFun y := ((torsionBinaryMulEquiv n hn).symm
    (Multiplicative.ofAdd y.1,Multiplicative.ofAdd y.2)).toAdd
  left_inv x := congrArg Multiplicative.toAdd
    ((torsionBinaryMulEquiv n hn).symm_apply_apply (Multiplicative.ofAdd x))
  right_inv y := congrArg (fun z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) =>
    (z.1.toAdd,z.2.toAdd)) ((torsionBinaryMulEquiv n hn).apply_symm_apply
      (Multiplicative.ofAdd y.1,Multiplicative.ofAdd y.2))
  map_add' x y := congrArg (fun z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) =>
    (z.1.toAdd,z.2.toAdd)) ((torsionBinaryMulEquiv n hn).map_mul
      (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

/-- A constructed perfect alternating form on the ACTUAL geometric E[2].
Its geometric Weil-pairing identification is not assumed or claimed here. -/
def originalTorsionPairing (n : F) (hn : n ≠ 0) (P Q : closedTwoTorsion n) : ZMod 2 :=
  binaryPairing (torsionBinaryEquiv n hn P) (torsionBinaryEquiv n hn Q)

lemma actual_original_pairing_add_left (n : F) (hn : n ≠ 0) (P Q R : closedTwoTorsion n) :
    originalTorsionPairing n hn (P+Q) R=originalTorsionPairing n hn P R+originalTorsionPairing n hn Q R := by
  simp only [originalTorsionPairing,map_add,actual_binary_pairing_add_left]

lemma actual_original_pairing_add_right (n : F) (hn : n ≠ 0) (P Q R : closedTwoTorsion n) :
    originalTorsionPairing n hn P (Q+R)=originalTorsionPairing n hn P Q+originalTorsionPairing n hn P R := by
  simp only [originalTorsionPairing,map_add,actual_binary_pairing_add_right]

lemma actual_original_pairing_alternating (n : F) (hn : n ≠ 0) (P : closedTwoTorsion n) :
    originalTorsionPairing n hn P P=0 := actual_binary_pairing_self _

lemma actual_original_pairing_nondegenerate (n : F) (hn : n ≠ 0) (P : closedTwoTorsion n)
    (hP : ∀ Q, originalTorsionPairing n hn P Q=0) : P=0 := by
  apply (torsionBinaryEquiv n hn).injective
  rw [map_zero]
  apply actual_binary_pairing_nondegenerate
  intro y
  obtain ⟨Q,rfl⟩ := (torsionBinaryEquiv n hn).surjective y
  exact hP Q

lemma actual_original_pairing_galois (n : F) (hn : n ≠ 0)
    (σ : Field.absoluteGaloisGroup F) (P Q : closedTwoTorsion n) :
    originalTorsionPairing n hn ((actualTwoTorsionRep n).ρ σ P) ((actualTwoTorsionRep n).ρ σ Q)=
      originalTorsionPairing n hn P Q := by
  rw [Representation.isTrivial_apply,Representation.isTrivial_apply]

end ActualTwoDescentOriginalTorsionPairing318
