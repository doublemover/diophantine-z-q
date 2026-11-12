module
public import ActualTwoDescentTorsionCoefficientTransfer318
public section
noncomputable section
namespace ActualTwoDescentContinuousCocycleRestriction318
set_option maxHeartbeats 16000000

open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentTorsionCoefficientTransfer318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

/-- Actual absolute-Galois restriction followed by the specified E[2] coefficient transfer. -/
def cocycleRestriction (f : F →+* L) (n : F) (hn : n ≠ 0) : continuousCocycles n →* continuousCocycles (f n) where
  toFun χ := ⟨(torsionCoefficientTransfer f n hn).comp
      ((χ : Field.absoluteGaloisGroup F →* Multiplicative (closedTwoTorsion n)).comp (Field.absoluteGaloisGroup.map f).toMonoidHom),
    (χ.property.comp_continuous (Field.absoluteGaloisGroup.map f).continuous).comp (torsionCoefficientTransfer f n hn)⟩
  map_one' := by
    apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact (torsionCoefficientTransfer f n hn).map_one
  map_mul' χ ψ := by
    apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact (torsionCoefficientTransfer f n hn).map_mul _ _

end ActualTwoDescentContinuousCocycleRestriction318
