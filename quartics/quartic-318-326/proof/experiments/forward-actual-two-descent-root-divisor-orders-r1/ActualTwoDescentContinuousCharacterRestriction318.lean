module
public import ActualTwoDescentClosureFieldEmbedding318
public section
noncomputable section
namespace ActualTwoDescentContinuousCharacterRestriction318
set_option maxHeartbeats 16000000

open ActualTwoDescentClosureFieldEmbedding318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldSquareOneMaps318 ActualTwoDescentFieldScalarConnectingHom318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

/-- Actual continuous restriction along Gal(L)→Gal(F), with the actual square-one coefficient embedding. -/
def characterRestriction (f : F →+* L) : continuousCharacters (F:=F) →* continuousCharacters (F:=L) where
  toFun χ := ⟨(squareOneMap (closureMap f)).comp
      ((χ : Field.absoluteGaloisGroup F →* SquareOne (AlgebraicClosure F)).comp (Field.absoluteGaloisGroup.map f).toMonoidHom),
    (χ.property.comp_continuous (Field.absoluteGaloisGroup.map f).continuous).comp (squareOneMap (closureMap f))⟩
  map_one' := by
    apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact (squareOneMap (closureMap f)).map_one
  map_mul' χ ψ := by
    apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact (squareOneMap (closureMap f)).map_mul _ _

def pairCharacterRestriction (f : F →+* L) :
    (continuousCharacters (F:=F) × continuousCharacters (F:=F)) →*
      (continuousCharacters (F:=L) × continuousCharacters (F:=L)) :=
  (characterRestriction f).prodMap (characterRestriction f)

end ActualTwoDescentContinuousCharacterRestriction318
