module
public import ActualTwoDescentFirstTorsionRootCharacter318
public section
noncomputable section
namespace ActualTwoDescentFirstTorsionGaloisComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentKummerHom318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentSquarePairGaloisEquivalence318 ActualTwoDescentScalarGaloisEquivalence318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentContinuousTorsionCoordinates318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentScalarRootCharacters318
open ActualTwoDescentScalarSquareRoots318 ActualTwoDescentHalfFlipTranslations318
open ActualTwoDescentHalvingChoiceIndependence318 ActualTwoDescentGaloisTwoTorsion318
open ActualTwoDescentTorsionSignHom318 ActualTwoDescentFirstTorsionGeometricHalf318
open ActualTwoDescentFirstTorsionRootCharacter318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_first_torsion_galois_comparison (n : ℚ) (hn : n ≠ 0) :
    cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd (firstTorsion n hn)))=
      squarePairGaloisEquiv (kummerClass n hn (firstTorsion n hn)) := by
  let a := scalarRoot (Units.mk0 n hn)
  have ha : a^2=algebraMap ℚ Qbar n := scalar_root_square _
  have han : a ≠ 0 := scalar_root_ne _
  let Q := rootHalf _ _ a 0 (2*a) (rational_parameter_ne n hn) ha
    (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
  have hhalf : Q+Q=ActualTwoDescentGaloisFixedRational318.rationalPointMap n hn (firstTorsion n hn) := actual_first_torsion_half n hn a ha
  rw [actual_first_torsion_class]
  change _=(scalarGaloisEquiv (ActualTwoDescentSquareClassQuotient318.classOf n hn),scalarGaloisEquiv 1)
  rw [actual_scalar_galois_value,map_one]
  have hσ (σ : GalQ) : torsionSignHom n hn (rationalHalvingCocycle n hn (firstTorsion n hn) σ)=
      (scalarCharacter (Units.mk0 n hn) σ,1) := by
    change ActualTwoDescentTorsionSignValues318.torsionSignValue _ _
      ((rationalHalvingCocycle n hn (firstTorsion n hn) σ).toAdd : Point _)=_
    rw [actual_halving_cocycle_evaluate n hn (firstTorsion n hn) Q hhalf]
    exact actual_first_torsion_root_character σ n hn a han ha
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (hσ σ)
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (hσ σ)

end ActualTwoDescentFirstTorsionGaloisComparison318
