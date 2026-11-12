module
public import ActualTwoDescentCupRestriction318
public section
noncomputable section
namespace ActualTwoDescentOriginalPerfectPairing318
open ActualTwoDescentBinarySymplectic318 ActualTwoDescentOriginalTorsionPairing318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentSquareOneBinary318
open ActualTwoDescentFieldSquareOneUnits318

def binaryPairingHom : BinaryPlane →+ (BinaryPlane →+ ZMod 2) where
  toFun x :=
    { toFun := binaryPairing x
      map_zero' := actual_binary_pairing_zero_right x
      map_add' := actual_binary_pairing_add_right x }
  map_zero' := by ext y; exact actual_binary_pairing_zero_left y
  map_add' x y := by ext z; exact actual_binary_pairing_add_left x y z

lemma actual_binary_pairing_hom_injective : Function.Injective binaryPairingHom := by
  intro x y h
  have h1 := congrArg (fun f : BinaryPlane →+ ZMod 2 => f (0,1)) h
  have h2 := congrArg (fun f : BinaryPlane →+ ZMod 2 => f (1,0)) h
  apply Prod.ext
  · simpa [binaryPairingHom,binaryPairing] using h1
  · simpa [binaryPairingHom,binaryPairing] using h2

lemma actual_binary_pairing_hom_surjective : Function.Surjective binaryPairingHom := by
  intro f
  refine ⟨(f (0,1),-f (1,0)),?_⟩
  apply AddMonoidHom.ext
  rintro ⟨a,b⟩
  fin_cases a <;> fin_cases b
  · simpa [binaryPairingHom,binaryPairing] using (map_zero f).symm
  · simp [binaryPairingHom,binaryPairing]
  · simp [binaryPairingHom,binaryPairing]
  · simpa [binaryPairingHom,binaryPairing,add_comm] using (map_add f (1,0) (0,1)).symm

def binaryPerfectPairing : BinaryPlane ≃+ (BinaryPlane →+ ZMod 2) :=
  AddEquiv.ofBijective binaryPairingHom
    ⟨actual_binary_pairing_hom_injective,actual_binary_pairing_hom_surjective⟩

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _

def originalTorsionDualCoordinates (n : F) (hn : n ≠ 0) :
    (closedTwoTorsion n →+ ZMod 2) ≃+ (BinaryPlane →+ ZMod 2) where
  toFun f := f.comp (torsionBinaryEquiv n hn).symm.toAddMonoidHom
  invFun f := f.comp (torsionBinaryEquiv n hn).toAddMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl

/-- Perfectness as an ACTUAL additive duality equivalence on original E[2],
not merely a cardinal count or a nondegeneracy predicate. -/
def originalTorsionPerfectPairing (n : F) (hn : n ≠ 0) :
    closedTwoTorsion n ≃+ (closedTwoTorsion n →+ ZMod 2) :=
  ((torsionBinaryEquiv n hn).trans binaryPerfectPairing).trans (originalTorsionDualCoordinates n hn).symm

lemma actual_original_perfect_pairing_value (n : F) (hn : n ≠ 0) (P Q : closedTwoTorsion n) :
    originalTorsionPerfectPairing n hn P Q=originalTorsionPairing n hn P Q := rfl

/-- The literal root-of-unity-valued version. The target is the ACTUAL
subgroup of (algebraic closure) units, not a symbol renamed mu_2. -/
def originalRootPairing (n : F) (hn : n ≠ 0) (P Q : closedTwoTorsion n) :
    SquareOne (AlgebraicClosure F) :=
  squareOneBinaryEquiv.symm (Multiplicative.ofAdd (originalTorsionPairing n hn P Q))

lemma actual_original_root_pairing_add_left (n : F) (hn : n ≠ 0) (P Q R : closedTwoTorsion n) :
    originalRootPairing n hn (P+Q) R=originalRootPairing n hn P R*originalRootPairing n hn Q R := by
  unfold originalRootPairing
  rw [actual_original_pairing_add_left]
  exact squareOneBinaryEquiv.symm.map_mul _ _

lemma actual_original_root_pairing_add_right (n : F) (hn : n ≠ 0) (P Q R : closedTwoTorsion n) :
    originalRootPairing n hn P (Q+R)=originalRootPairing n hn P Q*originalRootPairing n hn P R := by
  unfold originalRootPairing
  rw [actual_original_pairing_add_right]
  exact squareOneBinaryEquiv.symm.map_mul _ _

lemma actual_original_root_pairing_alternating (n : F) (hn : n ≠ 0) (P : closedTwoTorsion n) :
    originalRootPairing n hn P P=1 := by
  unfold originalRootPairing
  rw [actual_original_pairing_alternating]
  exact map_one squareOneBinaryEquiv.symm

end ActualTwoDescentOriginalPerfectPairing318
