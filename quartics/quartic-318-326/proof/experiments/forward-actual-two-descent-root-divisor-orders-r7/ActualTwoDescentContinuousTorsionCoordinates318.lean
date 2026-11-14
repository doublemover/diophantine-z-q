module
public import ActualTwoDescentGaloisHalfTranslations318
public section
noncomputable section
namespace ActualTwoDescentContinuousTorsionCoordinates318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentGaloisTwoTorsion318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentScalarConnectingHom318
open ActualTwoDescentSquareOneUnits318 ActualTwoDescentTorsionSignHom318 ActualTwoDescentTorsionSignEquivalence318

def cocyclePair (n : ℚ) (hn : n ≠ 0) (f : continuousCocycles n) : continuousCharacters × continuousCharacters :=
  (⟨((MonoidHom.fst _ _).comp (torsionSignHom n hn)).comp f,
      f.property.comp (fun T => (torsionSignHom n hn T).1)⟩,
    ⟨((MonoidHom.snd _ _).comp (torsionSignHom n hn)).comp f,
      f.property.comp (fun T => (torsionSignHom n hn T).2)⟩)

def cocycleOfPair (n : ℚ) (hn : n ≠ 0) (z : continuousCharacters × continuousCharacters) : continuousCocycles n :=
  ⟨(torsionSignEquiv n hn).symm.toMonoidHom.comp ((z.1 : GalQ →* SquareOne Qbar).prod z.2),
    (z.1.property.prodMk z.2.property).comp (torsionSignEquiv n hn).symm⟩

/-- Actual entire group of locally constant E[2]-cocycles, in the original(-3n,n) root basis. -/
def continuousTorsionCoordinates (n : ℚ) (hn : n ≠ 0) : continuousCocycles n ≃* (continuousCharacters × continuousCharacters) where
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

def continuousTorsionSquareclasses (n : ℚ) (hn : n ≠ 0) : continuousCocycles n ≃*
    (ActualTwoDescentSquareClassQuotient318.SquareClass ℚ × ActualTwoDescentSquareClassQuotient318.SquareClass ℚ) :=
  (continuousTorsionCoordinates n hn).trans ActualTwoDescentSquarePairGaloisEquivalence318.squarePairGaloisEquiv.symm

end ActualTwoDescentContinuousTorsionCoordinates318
