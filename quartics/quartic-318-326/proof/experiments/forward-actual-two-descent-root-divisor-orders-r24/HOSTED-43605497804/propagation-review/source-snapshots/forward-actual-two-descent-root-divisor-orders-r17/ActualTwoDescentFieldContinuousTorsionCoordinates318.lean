module
public import ActualTwoDescentFieldGaloisHalfTranslations318
public section
noncomputable section
namespace ActualTwoDescentFieldContinuousTorsionCoordinates318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldSquareOneUnits318 ActualTwoDescentFieldTorsionSignHom318 ActualTwoDescentFieldTorsionSignEquivalence318

def cocyclePair (n : F) (hn : n ≠ 0) (f : continuousCocycles n) : (continuousCharacters (F:=F)) × (continuousCharacters (F:=F)) :=
  (⟨((MonoidHom.fst _ _).comp (torsionSignHom n hn)).comp f,
      f.property.comp (fun T => (torsionSignHom n hn T).1)⟩,
    ⟨((MonoidHom.snd _ _).comp (torsionSignHom n hn)).comp f,
      f.property.comp (fun T => (torsionSignHom n hn T).2)⟩)

def cocycleOfPair (n : F) (hn : n ≠ 0) (z : (continuousCharacters (F:=F)) × (continuousCharacters (F:=F))) : continuousCocycles n :=
  ⟨(torsionSignEquiv n hn).symm.toMonoidHom.comp ((z.1 : GalQ →* SquareOne Qbar).prod z.2),
    (z.1.property.prodMk z.2.property).comp (torsionSignEquiv n hn).symm⟩

/-- Actual entire group of locally constant E[2]-cocycles, in the original(-3n,n) root basis. -/
def continuousTorsionCoordinates (n : F) (hn : n ≠ 0) : continuousCocycles n ≃* ((continuousCharacters (F:=F)) × (continuousCharacters (F:=F))) where
  toFun := cocyclePair n hn
  invFun := cocycleOfPair n hn
  left_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro σ
    exact (torsionSignEquiv n hn).symm_apply_apply ((f : GalQ →* Multiplicative (closedTwoTorsion n)) σ)
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext; apply MonoidHom.ext; intro σ
      exact congrArg Prod.fst ((torsionSignEquiv n hn).apply_symm_apply ((z.1 : GalQ →* SquareOne Qbar) σ,(z.2 : GalQ →* SquareOne Qbar) σ))
    · apply Subtype.ext; apply MonoidHom.ext; intro σ
      exact congrArg Prod.snd ((torsionSignEquiv n hn).apply_symm_apply ((z.1 : GalQ →* SquareOne Qbar) σ,(z.2 : GalQ →* SquareOne Qbar) σ))
  map_mul' f g := by
    apply Prod.ext
    · apply Subtype.ext; apply MonoidHom.ext; intro σ
      exact congrArg Prod.fst ((torsionSignHom n hn).map_mul ((f : GalQ →* Multiplicative (closedTwoTorsion n)) σ) ((g : GalQ →* Multiplicative (closedTwoTorsion n)) σ))
    · apply Subtype.ext; apply MonoidHom.ext; intro σ
      exact congrArg Prod.snd ((torsionSignHom n hn).map_mul ((f : GalQ →* Multiplicative (closedTwoTorsion n)) σ) ((g : GalQ →* Multiplicative (closedTwoTorsion n)) σ))

def continuousTorsionSquareclasses (n : F) (hn : n ≠ 0) : continuousCocycles n ≃*
    (ActualTwoDescentSquareClassQuotient318.SquareClass F × ActualTwoDescentSquareClassQuotient318.SquareClass F) :=
  (continuousTorsionCoordinates n hn).trans (ActualTwoDescentFieldSquarePairGaloisEquivalence318.squarePairGaloisEquiv (F:=F)).symm

end ActualTwoDescentFieldContinuousTorsionCoordinates318
