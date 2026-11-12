module
public import ActualTwoDescentOriginalFunctionFieldTheta318
public section
noncomputable section
namespace ActualTwoDescentOriginalThetaPairingComparison318
open ActualTwoDescentEllipticModel318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalTorsionPairing318 ActualTwoDescentOriginalPerfectPairing318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentFieldTorsionAdditionTable318 ActualTwoDescentFieldTorsionSignValues318
open ActualTwoDescentFieldTorsionSignHom318 ActualTwoDescentFieldTorsionSignEquivalence318
open ActualTwoDescentSquareOneBinary318 ActualTwoDescentBinarySymplectic318
open ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentOriginalFunctionFieldTheta318 ActualTwoDescentOriginalThetaMultipliers318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _

/-- Actual affine root points as elements of the original geometric E[2]. -/
def geometricRoot (n : F) (hn : n ≠ 0) (i : Fin 3) : closedTwoTorsion n :=
  ⟨rootPoint (algebraMap F (AlgebraicClosure F) n) (rational_parameter_ne n hn) i,by
    rw [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul]
    fin_cases i
    · exact actual_zero_torsion_double _ _
    · exact actual_first_torsion_double _ _
    · exact actual_torsion_double_zero _ _⟩

lemma actual_geometric_root_binary (n : F) (hn : n ≠ 0) (i : Fin 3) :
    torsionBinaryEquiv n hn (geometricRoot n hn i)=(![(1,1),(1,0),(0,1)] : Fin 3 → BinaryPlane) i := by
  change (squareOneBit (torsionSignValue _ _ (rootPoint _ _ i)).1,
    squareOneBit (torsionSignValue _ _ (rootPoint _ _ i)).2)=_
  fin_cases i
  · change (squareOneBit (torsionSignValue _ _ (zeroTorsion _ _)).1,
      squareOneBit (torsionSignValue _ _ (zeroTorsion _ _)).2)=_
    rw [actual_sign_zero_torsion]
    simp
  · change (squareOneBit (torsionSignValue _ _ (firstTorsion _ _)).1,
      squareOneBit (torsionSignValue _ _ (firstTorsion _ _)).2)=_
    rw [actual_sign_first_torsion]
    simp
  · change (squareOneBit (torsionSignValue _ _ (torsionPoint _ _)).1,
      squareOneBit (torsionSignValue _ _ (torsionPoint _ _)).2)=_
    rw [actual_sign_last_torsion]
    simp

lemma actual_original_root_pairing_table (n : F) (hn : n ≠ 0) (i j : Fin 3) :
    (((originalRootPairing n hn (geometricRoot n hn i) (geometricRoot n hn j) :
      SquareOne (AlgebraicClosure F)) : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)=
      if i=j then 1 else -1 := by
  unfold originalRootPairing originalTorsionPairing
  rw [actual_geometric_root_binary,actual_geometric_root_binary]
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryPairing,squareOneBinaryEquiv,binarySquareOne,negativeOne]

/-- Exact comparison of the original cup coefficient form with the
computed rational-function commutator, at all actual nonzero torsion pairs.
The projective-divisor/line-bundle interpretation is still a separate obligation. -/
theorem actual_original_pairing_native_commutator (n : F) (hn : n ≠ 0) (i j : Fin 3) :
    functionCoefficientMap (algebraMap F (AlgebraicClosure F) n)
      ((((originalRootPairing n hn (geometricRoot n hn i) (geometricRoot n hn j) :
        SquareOne (AlgebraicClosure F)) : (AlgebraicClosure F)ˣ) : AlgebraicClosure F))=
    thetaCommutator
      (functionCoefficientMap (algebraMap F (AlgebraicClosure F) n)
        (algebraMap F (AlgebraicClosure F) n))
      (functionX (algebraMap F (AlgebraicClosure F) n)) i j := by
  rw [actual_original_root_pairing_table,actual_native_theta_commutator _ (rational_parameter_ne n hn)]
  split_ifs <;> simp

end ActualTwoDescentOriginalThetaPairingComparison318
