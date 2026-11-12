module
public import ActualTwoDescentEllipticRestrictionNaturality318
public section
noncomputable section
namespace ActualTwoDescentTorsionTransferCoordinates318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldSquareOneUnits318 ActualTwoDescentFieldSquareOneMaps318
open ActualTwoDescentFieldTorsionSignValues318 ActualTwoDescentFieldTorsionSignEquivalence318
open ActualTwoDescentTorsionCoefficientTransfer318 ActualTwoDescentClosureFieldEmbedding318
open ActualTwoDescentFieldAlgebraicClosureHalving318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

def torsionLabel (n : F) (hn : n ≠ 0) (i : Fin 4) : Multiplicative (closedTwoTorsion n) :=
  Multiplicative.ofAdd ⟨ActualTwoDescentFinitePointCardinality318.fourTorsion (algebraMap F (AlgebraicClosure F) n) (rational_parameter_ne n hn) i,by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using
      ActualTwoDescentFinitePointCardinality318.actual_four_torsion_double _ (rational_parameter_ne n hn) i⟩

lemma actual_square_one_map_negative (f : F →+* L) : squareOneMap f (negativeOne : SquareOne F)=negativeOne := by
  apply Subtype.ext; apply Units.ext
  change f (-1)= -1
  rw [map_neg,map_one]

/-- Every geometric two-torsion label transfers to the SAME original root label. -/
lemma actual_torsion_transfer_label (f : F →+* L) (n : F) (hn : n ≠ 0) (i : Fin 4) :
    torsionCoefficientTransfer f n hn (torsionLabel n hn i)=
      torsionLabel (f n) (ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero f hn) i := by
  apply (torsionSignEquiv (f n) (ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero f hn)).injective
  rw [actual_torsion_transfer_signs]
  fin_cases i
  all_goals
    simp only [torsionLabel,ActualTwoDescentFinitePointCardinality318.fourTorsion,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    change ((squareOneMap (closureMap f)) (torsionSignValue _ _ _).1,
      (squareOneMap (closureMap f)) (torsionSignValue _ _ _).2)=torsionSignValue _ _ _
    simp only [actual_sign_zero,actual_sign_zero_torsion,actual_sign_first_torsion,actual_sign_last_torsion,
      map_one,actual_square_one_map_negative]

/-- The coefficient transfer is the LITERAL base change of BOTH original affine coordinates on ALL E[2]. -/
theorem actual_torsion_transfer_coordinates (f : F →+* L) (n : F) (hn : n ≠ 0)
    (T : Multiplicative (closedTwoTorsion n)) :
    ActualTwoDescentFinitePointCardinality318.pointCoordinates (algebraMap L (AlgebraicClosure L) (f n))
      (torsionCoefficientTransfer f n hn T).toAdd=
    Option.map (fun z : AlgebraicClosure F × AlgebraicClosure F => (closureMap f z.1,closureMap f z.2))
      (ActualTwoDescentFinitePointCardinality318.pointCoordinates (algebraMap F (AlgebraicClosure F) n) T.toAdd) := by
  have hT : (T.toAdd : Point (algebraMap F (AlgebraicClosure F) n))+(T.toAdd : Point (algebraMap F (AlgebraicClosure F) n))=0 := by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using T.toAdd.property
  obtain ⟨i,hi⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion _ (rational_parameter_ne n hn) T.toAdd hT
  have he : T=torsionLabel n hn i := Subtype.ext hi
  rw [he,actual_torsion_transfer_label]
  fin_cases i
  all_goals
    simp only [torsionLabel,ActualTwoDescentFinitePointCardinality318.fourTorsion,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      ActualTwoDescentFinitePointCardinality318.pointCoordinates,ActualTwoDescentFiniteEllipticModel318.point,
      Option.map_none,Option.map_some,map_zero,map_mul,map_neg,map_ofNat,actual_closure_map_base]

end ActualTwoDescentTorsionTransferCoordinates318
