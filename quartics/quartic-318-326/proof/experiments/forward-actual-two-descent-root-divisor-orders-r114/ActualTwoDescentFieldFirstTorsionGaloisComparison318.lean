module
public import ActualTwoDescentFieldFirstTorsionRootCharacter318
public section
noncomputable section
namespace ActualTwoDescentFieldFirstTorsionGaloisComparison318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentKummerHom318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentFieldSquarePairGaloisEquivalence318 ActualTwoDescentFieldScalarGaloisEquivalence318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldScalarConnectingHom318 ActualTwoDescentFieldScalarRootCharacters318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldHalfFlipTranslations318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldTorsionSignHom318 ActualTwoDescentFieldFirstTorsionGeometricHalf318
open ActualTwoDescentFieldFirstTorsionRootCharacter318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_first_torsion_galois_comparison (n : F) (hn : n ≠ 0) :
    cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd (firstTorsion n hn)))=
      (squarePairGaloisEquiv (F:=F)) (kummerClass n hn (firstTorsion n hn)) := by
  let a := scalarRoot (Units.mk0 n hn)
  have ha : a^2=algebraMap F Qbar n := scalar_root_square _
  have han : a ≠ 0 := scalar_root_ne _
  let Q := rootHalf _ _ a 0 (2*a) (rational_parameter_ne n hn) ha
    (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
  have hhalf : Q+Q=ActualTwoDescentFieldGaloisFixedRational318.rationalPointMap n hn (firstTorsion n hn) := actual_first_torsion_half n hn a ha
  rw [actual_first_torsion_class]
  change _=((scalarGaloisEquiv (F:=F)) (ActualTwoDescentSquareClassQuotient318.classOf n hn),(scalarGaloisEquiv (F:=F)) 1)
  rw [actual_scalar_galois_value,map_one]
  have hσ (σ : GalQ) : torsionSignHom n hn (rationalHalvingCocycle n hn (firstTorsion n hn) σ)=
      (scalarCharacter (Units.mk0 n hn) σ,1) := by
    change ActualTwoDescentFieldTorsionSignValues318.torsionSignValue _ _
      ((rationalHalvingCocycle n hn (firstTorsion n hn) σ).toAdd : Point _)=_
    rw [actual_halving_cocycle_evaluate n hn (firstTorsion n hn) Q hhalf]
    exact actual_first_torsion_root_character σ n hn a han ha
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (hσ σ)
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (hσ σ)

end ActualTwoDescentFieldFirstTorsionGaloisComparison318
