module
public import ActualTwoDescentLastTorsionRootCharacters318
public section
noncomputable section
namespace ActualTwoDescentLastTorsionGaloisComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentKummerHom318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentSquarePairGaloisEquivalence318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentContinuousTorsionCoordinates318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentScalarRootCharacters318
open ActualTwoDescentScalarSquareRoots318 ActualTwoDescentHalfFlipTranslations318
open ActualTwoDescentHalvingChoiceIndependence318 ActualTwoDescentGaloisTwoTorsion318
open ActualTwoDescentTorsionSignHom318 ActualTwoDescentLastTorsionGeometricHalf318
open ActualTwoDescentLastTorsionRootCharacters318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_last_torsion_galois_comparison (n : ℚ) (hn : n ≠ 0) :
    cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd (torsionPoint n hn)))=
      squarePairGaloisEquiv (kummerClass n hn (torsionPoint n hn)) := by
  let u := scalarRoot (Units.mk0 (3 : ℚ) (by norm_num))
  let v := scalarRoot (Units.mk0 (-n) (neg_ne_zero.mpr hn))
  have hu : u^2=3 := by simpa only [Units.val_mk0,map_ofNat] using scalar_root_square (Units.mk0 (3 : ℚ) (by norm_num))
  have hv : v^2= -algebraMap ℚ Qbar n := by
    simpa only [Units.val_mk0,map_neg] using scalar_root_square (Units.mk0 (-n) (neg_ne_zero.mpr hn))
  have hun : u ≠ 0 := scalar_root_ne _
  have hvn : v ≠ 0 := scalar_root_ne _
  let Q := rootHalf _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
    (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1 (actual_last_half_roots n u v hu hv).2.2
  have hhalf : Q+Q=ActualTwoDescentGaloisFixedRational318.rationalPointMap n hn (torsionPoint n hn) := actual_last_torsion_half n hn u v hu hv
  rw [actual_second_torsion_class]
  change _=squarePairGaloisEquiv (ActualTwoDescentSquareClassQuotient318.classOf 3 (by norm_num),
    ActualTwoDescentSquareClassQuotient318.classOf (-n) (neg_ne_zero.mpr hn))
  rw [actual_squarepair_galois_value]
  have hσ (σ : GalQ) : torsionSignHom n hn (rationalHalvingCocycle n hn (torsionPoint n hn) σ)=
      (scalarCharacter (Units.mk0 3 (by norm_num)) σ,scalarCharacter (Units.mk0 (-n) (neg_ne_zero.mpr hn)) σ) := by
    change ActualTwoDescentTorsionSignValues318.torsionSignValue _ _
      ((rationalHalvingCocycle n hn (torsionPoint n hn) σ).toAdd : Point _)=_
    rw [actual_halving_cocycle_evaluate n hn (torsionPoint n hn) Q hhalf]
    exact actual_last_torsion_root_characters σ n hn u v hun hvn hu hv
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (hσ σ)
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (hσ σ)

end ActualTwoDescentLastTorsionGaloisComparison318
