module
public import ActualTwoDescentContinuousCocycleRestriction318
public section
noncomputable section
namespace ActualTwoDescentCocycleRestrictionCoordinates318
set_option maxHeartbeats 16000000

open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentFieldContinuousTorsionCoordinates318 ActualTwoDescentContinuousCharacterRestriction318
open ActualTwoDescentTorsionCoefficientTransfer318 ActualTwoDescentContinuousCocycleRestriction318
open ActualTwoDescentFieldSquarePairGaloisEquivalence318 ActualTwoDescentSquareclassRestrictionNaturality318
open ActualTwoDescentSquareClassFieldMap318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

lemma actual_cocycle_restriction_coordinates (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    cocyclePair (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ)=
      pairCharacterRestriction f (cocyclePair n hn χ) := by
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (actual_torsion_transfer_signs f n hn ((χ : Field.absoluteGaloisGroup F →* Multiplicative (closedTwoTorsion n)) (Field.absoluteGaloisGroup.map f σ)))
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (actual_torsion_transfer_signs f n hn ((χ : Field.absoluteGaloisGroup F →* Multiplicative (closedTwoTorsion n)) (Field.absoluteGaloisGroup.map f σ)))

/-- Actual restriction commutes with the actual original squareclass maps. -/
theorem actual_cocycle_restriction_squareclasses (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    continuousTorsionSquareclasses (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ)=
      squarePairMap f (continuousTorsionSquareclasses n hn χ) := by
  apply (squarePairGaloisEquiv (F:=L)).injective
  change squarePairGaloisEquiv (F:=L) ((squarePairGaloisEquiv (F:=L)).symm
      (cocyclePair (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ)))=
    squarePairGaloisEquiv (F:=L) (squarePairMap f ((squarePairGaloisEquiv (F:=F)).symm (cocyclePair n hn χ)))
  rw [(squarePairGaloisEquiv (F:=L)).apply_symm_apply,actual_pair_equiv_restriction,
    (squarePairGaloisEquiv (F:=F)).apply_symm_apply]
  exact actual_cocycle_restriction_coordinates f n hn χ

end ActualTwoDescentCocycleRestrictionCoordinates318
