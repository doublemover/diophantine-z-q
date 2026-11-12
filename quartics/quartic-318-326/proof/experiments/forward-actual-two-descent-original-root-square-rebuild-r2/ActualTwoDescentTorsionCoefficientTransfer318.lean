module
public import ActualTwoDescentSquareclassRestrictionNaturality318
public section
noncomputable section
namespace ActualTwoDescentTorsionCoefficientTransfer318
set_option maxHeartbeats 16000000

open ActualTwoDescentClosureFieldEmbedding318 ActualTwoDescentFieldSquareOneMaps318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldTorsionSignEquivalence318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

def torsionCoefficientTransfer (f : F →+* L) (n : F) (hn : n ≠ 0) :
    Multiplicative (closedTwoTorsion n) →* Multiplicative (closedTwoTorsion (f n)) :=
  (torsionSignEquiv (f n) (ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero f hn)).symm.toMonoidHom.comp
    (((squareOneMap (closureMap f)).prodMap (squareOneMap (closureMap f))).comp (torsionSignEquiv n hn).toMonoidHom)

lemma actual_torsion_transfer_signs (f : F →+* L) (n : F) (hn : n ≠ 0)
    (T : Multiplicative (closedTwoTorsion n)) :
    torsionSignEquiv (f n) (ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero f hn)
      (torsionCoefficientTransfer f n hn T)=
      ((squareOneMap (closureMap f)) (torsionSignEquiv n hn T).1,
       (squareOneMap (closureMap f)) (torsionSignEquiv n hn T).2) :=
  (torsionSignEquiv (f n) _).apply_symm_apply _

end ActualTwoDescentTorsionCoefficientTransfer318
