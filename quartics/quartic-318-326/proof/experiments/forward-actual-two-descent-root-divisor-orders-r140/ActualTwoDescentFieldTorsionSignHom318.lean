module
public import ActualTwoDescentFieldTorsionSignValues318
public section
noncomputable section
namespace ActualTwoDescentFieldTorsionSignHom318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentActualTorsionPoint318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldTorsionAdditionTable318 ActualTwoDescentFieldTorsionSignValues318
open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldGaloisTwoTorsion318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_torsion_sign_add (n : Qbar) (hn : n ≠ 0) (P Q : Point n) (hP : P+P=0) (hQ : Q+Q=0) :
    torsionSignValue n hn (P+Q)=torsionSignValue n hn P*torsionSignValue n hn Q := by
  obtain ⟨i,rfl⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion n hn P hP
  obtain ⟨j,rfl⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion n hn Q hQ
  have h10 := (add_comm (firstTorsion n hn) (zeroTorsion n hn)).trans (actual_zero_first_sum n hn)
  have h20 := (add_comm (torsionPoint n hn) (zeroTorsion n hn)).trans (actual_zero_last_sum n hn)
  have h21 := (add_comm (torsionPoint n hn) (firstTorsion n hn)).trans (actual_first_last_sum n hn)
  fin_cases i <;> fin_cases j
  all_goals
    change torsionSignValue n hn (_+_)=torsionSignValue n hn _*torsionSignValue n hn _
    simp only [ActualTwoDescentFinitePointCardinality318.fourTorsion,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    change torsionSignValue n hn (_+_)=torsionSignValue n hn _*torsionSignValue n hn _
    simp only [zero_add,add_zero,actual_zero_torsion_double,actual_first_torsion_double,
      actual_torsion_double_zero,actual_zero_first_sum,actual_zero_last_sum,actual_first_last_sum,h10,h20,h21,
      actual_sign_zero,actual_sign_zero_torsion,actual_sign_first_torsion,actual_sign_last_torsion]
  all_goals
    apply Prod.ext <;> apply Subtype.ext <;> apply Units.ext <;> norm_num [negativeOne]

def torsionSignHom (n : F) (hn : n ≠ 0) : Multiplicative (closedTwoTorsion n) →* (SquareOne Qbar × SquareOne Qbar) where
  toFun T := torsionSignValue (algebraMap F Qbar n) (rational_parameter_ne n hn) T.toAdd
  map_one' := actual_sign_zero _ _
  map_mul' T U := by
    apply actual_torsion_sign_add
    · simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using T.toAdd.property
    · simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using U.toAdd.property

end ActualTwoDescentFieldTorsionSignHom318
